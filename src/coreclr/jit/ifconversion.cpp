// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

/*XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XX                                                                           XX
XX                              OptIfConversion                              XX
XX                                                                           XX
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
*/

#include "jitpch.h"
#ifdef _MSC_VER
#pragma hdrstop
#endif

//-----------------------------------------------------------------------------
// OptIfConversionDsc:     Descriptor used for If conversion
//
class OptIfConversionDsc
{
public:
    OptIfConversionDsc(Compiler* comp, BasicBlock* jtrueBlock)
    {
        m_compiler   = comp;
        m_jtrueBlock = jtrueBlock;
    }

private:
    Compiler*   m_compiler;    // The Compiler instance.
    BasicBlock* m_jtrueBlock;  // First block in the If Conversion.

    // The node, statement and block of an operation.
    struct IfConvertOperation
    {
        BasicBlock* block = nullptr;
        Statement*  stmt  = nullptr;
        GenTree*    node  = nullptr;
    };

    IfConvertOperation m_thenOperation;       // The single operation in the Then case.
    IfConvertOperation m_elseOperation;       // The single operation in the Else case.
    BasicBlock*        m_flowsMergeBlock;     // The block where Then and Else flows merge. In a return case, this can be nullptr.
    genTreeOps         m_OperationType = GT_COUNT; // The main operation of the if conversion. Store or Return.

    bool TryGetTransformationDsc();
    bool TryGetOperation(BasicBlock*         fromBlock,
                         BasicBlock*         toBlock,
                         IfConvertOperation* operation,
                         bool                conditionHasSideEffects);
    bool IsProfitable(int* pReachabilityBudget);

    GenTree* TryTransformSelectOperOrLocal(GenTree* condition, GenTree* oper, GenTree* lcl);
    GenTree* TryTransformSelectOperOrZero(GenTree* condition, GenTree* oper, GenTree* lcl);
    GenTree* TryTransformSelectToOrdinaryOps(GenTree* condition, GenTree* trueInput, GenTree* falseInput);

    bool DoElseConversion() const
    {
        return m_elseOperation.block != nullptr;
    }

    bool HasExplicitElseBlock() const
    {
        return DoElseConversion() && m_elseOperation.block != m_jtrueBlock;
    }

#ifdef DEBUG
    void Dump();
#endif

public:
    bool optIfConvert(int* pReachabilityBudget);
};

bool OptIfConversionDsc::TryGetTransformationDsc()
{
    genTreeOps mainOper = GT_STORE_LCL_VAR;
    BasicBlock* flowsMergeBlock = m_jtrueBlock->GetTrueTarget();
    IfConvertOperation thenOperation;
    IfConvertOperation elseOperation;

    const int blockLimit = 4; // Max number of blocks in a Then/Else case to walk before giving up

    bool hasElseCase = m_jtrueBlock->GetTrueTarget()->GetUniquePred(m_compiler) != nullptr;
    if (hasElseCase)
    {
        // Walk the Else blocks until we exit the region and
        // receive flow from the Then case. This will be the block where flows merge
        BasicBlock* block = m_jtrueBlock->GetTrueTarget();
        int budget = blockLimit;
        while (block->GetUniquePred(m_compiler) != nullptr)
        {
            if (budget-- <= 0)
            {
                return false;
            }

            BasicBlock* nextBlock = block->GetUniqueSucc();
            flowsMergeBlock = nextBlock;
            
            if (nextBlock == nullptr)
            {
                if (block->KindIs(BBJ_RETURN))
                {
                    mainOper = GT_RETURN;
                    break;
                }
    
                // Flow diverges
                return false;
            }
            
            block = nextBlock;
        }
    }

    {
        // Walk the Then blocks until we exit the region and
        // reach the block where both flows merge
        BasicBlock* block = m_jtrueBlock->GetFalseTarget();
        int budget = blockLimit;
        while (true)
        {
            if (budget-- <= 0)
            {
                return false;
            }

            if (block->GetUniquePred(m_compiler) == nullptr)
            {
                return false;
            }

            block = block->GetUniqueSucc();
            if (block == flowsMergeBlock)
            {
                break;
            }

            if (block == nullptr)
            {
                return false;
            }
        }
    }

    GenTree* condition               = m_jtrueBlock->lastStmt()->GetRootNode()->gtGetOp1();
    bool     conditionHasSideEffects = ((condition->gtFlags & GTF_ORDER_SIDEEFF) != 0);
    if (!TryGetOperation(m_jtrueBlock->GetFalseTarget(), flowsMergeBlock, &thenOperation, conditionHasSideEffects))
    {
        return false;
    }

    if (hasElseCase)
    {
        if (!TryGetOperation(m_jtrueBlock->GetTrueTarget(), flowsMergeBlock, &elseOperation, conditionHasSideEffects))
        {
            return false;
        }
    }

    if (hasElseCase)
    {
        // Both operations must be the same node type.
        if (thenOperation.node->OperGet() != elseOperation.node->OperGet())
        {
            return false;
        }

        // Currently can only support Else store blocks that have the same destination as the Then block.
        if (thenOperation.node->OperIs(GT_STORE_LCL_VAR))
        {
            unsigned lclNumThen = thenOperation.node->AsLclVarCommon()->GetLclNum();
            unsigned lclNumElse = elseOperation.node->AsLclVarCommon()->GetLclNum();
            if (lclNumThen != lclNumElse)
            {
                return false;
            }
        }
    }

    m_thenOperation = thenOperation;
    m_elseOperation = elseOperation;
    m_flowsMergeBlock = flowsMergeBlock;
    m_OperationType        = mainOper;

    return true;
}


//-----------------------------------------------------------------------------
// TryGetOperation
//
// From the given block to the final block, check all the statements and nodes are
// valid for an If conversion. Chain of blocks must contain only a single local
// store and no other operations.
//
// Arguments:
//   fromBlock      - Block inside the if statement to start from (Either Then or Else path).
//   operation - Returns the found operation.
//
// Returns:
//   If everything is valid, then set operation to the store and return true.
//   Otherwise return false.
//
bool OptIfConversionDsc::TryGetOperation(BasicBlock*         fromBlock,
                                         BasicBlock*         toBlock,
                                         IfConvertOperation* foundOperation,
                                         bool                conditionHasSideEffects)
{    
    bool found = false; 

    for (BasicBlock* block = fromBlock; block != toBlock; block = block->GetUniqueSucc())
    {
        // Can all the nodes within the block be made to conditionally execute?
        for (Statement* stmt : fromBlock->Statements())
        {
            GenTree* tree = stmt->GetRootNode();
            if (tree->OperIs(GT_STORE_LCL_VAR, GT_RETURN))
            {
                // Operation has multiple statements which is not supported by SELECT
                if (found)
                {
                    return false;
                }

                // Ensure the operation has integer type.
                if (!varTypeIsIntegralOrI(tree))
                {
                    return false;
                }

#ifndef TARGET_64BIT
                // Disallow 64-bit operands on 32-bit targets as the backend currently cannot
                // handle contained relops efficiently after decomposition.
                if (varTypeIsLong(tree))
                {
                    return false;
                }
#endif

                GenTree* store = tree->gtGetOp1();

                // Ensure it won't cause any additional side effects.
                if ((store->gtFlags & (GTF_SIDE_EFFECT | GTF_ORDER_SIDEEFF)) != 0)
                {
                    return false;
                }

                // Evaluating unconditionally effectively has the same effect as reordering
                // with the condition (for example, the condition could be an explicit bounds
                // check and the operand could read an array element). Disallow this except
                // for some common cases that we know are always side effect free.
                if (conditionHasSideEffects && !store->IsInvariant() && !store->OperIsLocal())
                {
                    return false;
                }

                found = true;
                foundOperation->block = block;
                foundOperation->stmt  = stmt;
                foundOperation->node  = tree;
            }
            else if (!tree->OperIs(GT_NOP))
            {
                // Cannot optimise this block.
                return false;
            }
        }
    }

    return found;
}

bool OptIfConversionDsc::IsProfitable(int* pReachabilityBudget)
{
    // Using SELECT nodes means that both Then and Else operations are fully evaluated.
    // Put a limit on the original source and destinations.
    if (!m_compiler->compStressCompile(Compiler::STRESS_IF_CONVERSION_COST, 25))
    {
        int thenCost = 0;
        int elseCost = 0;

        if (m_OperationType == GT_STORE_LCL_VAR)
        {
            thenCost = m_thenOperation.node->AsLclVar()->Data()->GetCostEx() +
                       (m_compiler->gtIsLikelyRegVar(m_thenOperation.node) ? 0 : 2);
            if (DoElseConversion())
            {
                elseCost = m_elseOperation.node->AsLclVar()->Data()->GetCostEx() +
                           (m_compiler->gtIsLikelyRegVar(m_elseOperation.node) ? 0 : 2);
            }
        }
        else
        {
            assert(m_OperationType == GT_RETURN);
            thenCost = m_thenOperation.node->AsOp()->GetReturnValue()->GetCostEx();
            if (DoElseConversion())
            {
                elseCost = m_elseOperation.node->AsOp()->GetReturnValue()->GetCostEx();
            }
        }

        // Cost to allow for "x = condition ? a + b : c + d".
        if (thenCost > 7 || elseCost > 7)
        {
            JITDUMP("Skipping if-conversion that will evaluate RHS unconditionally at costs %d,%d\n", thenCost,
                    elseCost);
            return false;
        }
    }

    if (!m_compiler->compStressCompile(Compiler::STRESS_IF_CONVERSION_INNER_LOOPS, 25))
    {
        // Don't optimise the block if it is inside a loop. Loop-carried
        // dependencies can cause significant stalls if if-converted.
        // Detect via the block weight as that will be high when inside a loop.

        if (m_jtrueBlock->getBBWeight(m_compiler) > BB_UNITY_WEIGHT * 1.05)
        {
            JITDUMP("Skipping if-conversion inside loop (via weight)\n");
            return false;
        }

        // We may be inside an unnatural loop, so do the expensive check.
        Compiler::ReachabilityResult reachability =
            m_compiler->optReachableWithBudget(m_flowsMergeBlock, m_jtrueBlock, nullptr, pReachabilityBudget);
        if (reachability == Compiler::ReachabilityResult::Reachable)
        {
            JITDUMP("Skipping if-conversion inside loop (via reachability)\n");
            return false;
        }
        else if (reachability == Compiler::ReachabilityResult::BudgetExceeded)
        {
            JITDUMP("Skipping if-conversion since we ran out of reachability budget\n");
            return false;
        }
    }

    return true;
}

//-----------------------------------------------------------------------------
// Dump
//
// Dump all the blocks in the If Conversion.
//
#ifdef DEBUG
void OptIfConversionDsc::Dump()
{
    m_compiler->fgDumpBlock(m_jtrueBlock);

    bool beforeTransformation = m_jtrueBlock->KindIs(BBJ_COND);
    if (beforeTransformation)
    {
        // Dump all Then blocks
        for (BasicBlock* bb = m_jtrueBlock->GetFalseTarget(); bb != m_flowsMergeBlock; bb = bb->GetUniqueSucc())
        {
            m_compiler->fgDumpBlock(bb);
        }

        if (DoElseConversion())
        {
            // Dump all Else blocks
            for (BasicBlock* bb = m_jtrueBlock->GetTrueTarget(); bb != m_flowsMergeBlock; bb = bb->GetUniqueSucc())
            {
                m_compiler->fgDumpBlock(bb);
            }
        }
    }
}
#endif

//-----------------------------------------------------------------------------
// optIfConvert
//
// Find blocks representing simple if statements represented by conditional jumps
// over another block. Try to replace the jumps by use of SELECT nodes.
//
// Arguments:
//   pReachabilityBudget -- budget for optReachability
//
// Returns:
//   true if any IR changes possibly made.
//
// Notes:
//
// Example of simple if conversion:
//
// This is optimising a simple if statement. There is a single condition being
// tested, and a single assignment inside the body. There must be no else
// statement. For example:
// if (x < 7) { a = 5; }
//
// This is represented in IR by two basic blocks. The first block (block) ends with
// a JTRUE statement which conditionally jumps to the second block (thenBlock).
// The second block just contains a single store statement. Both blocks then jump
// to the same destination (finalBlock).  Note that the first block may contain
// additional statements prior to the JTRUE statement.
//
// For example:
//
// ------------ BB03 [009..00D) -> BB05 (condition), preds={BB02} succs={BB04,BB05}
// STMT00004
//   *  JTRUE     void   $VN.Void
//   \--*  GE        int    $102
//      +--*  LCL_VAR   int    V02
//      \--*  CNS_INT   int    7 $46
//
// ------------ BB04 [00D..010), preds={BB03} succs={BB05}
// STMT00005
//   *  STORE_LCL_VAR   int    V00 arg0
//   \--*  CNS_INT   int    5 $47
//
//
// This is optimised by conditionally executing the store and removing the conditional
// jumps. First the JTRUE is replaced with a NOP. The store is updated so that the
// source of the store is a SELECT node with the condition set to the inverse of the
// original JTRUE condition. If the condition passes the original store happens,
// otherwise the existing source value is used.
//
// In the example above, local var 0 is set to 5 if the LT returns true, otherwise
// the existing value of local var 0 is used:
//
// ------------ BB03 [009..00D) -> BB05 (always), preds={BB02} succs={BB05}
// STMT00004
//   *  NOP       void
//
// STMT00005
//   *  STORE_LCL_VAR   int    V00 arg0
//   \--*  SELECT    int
//      +--*  LT        int    $102
//      |  +--*  LCL_VAR   int    V02
//      |  \--*  CNS_INT   int    7 $46
//      +--*  CNS_INT   int    5 $47
//      \--*  LCL_VAR   int    V00
//
// ------------ BB04 [00D..010), preds={} succs={BB05}
//
//
// Example of simple if conversion with an else condition
//
// This is similar to the simple if conversion above, but with an else statement
// that assigns to the same variable as the then statement. For example:
// if (x < 7) { a = 5; } else { a = 9; }
//
// ------------ BB03 [009..00D) -> BB05 (condition), preds={BB02} succs={BB04,BB05}
// STMT00004
//   *  JTRUE     void   $VN.Void
//   \--*  GE        int    $102
//      +--*  LCL_VAR   int    V02
//      \--*  CNS_INT   int    7 $46
//
// ------------ BB04 [00D..010), preds={BB03} succs={BB06}
// STMT00005
//   *  STORE_LCL_VAR   int    V00 arg0
//   \--*  CNS_INT   int    5 $47
//
// ------------ BB05 [00D..010), preds={BB03} succs={BB06}
// STMT00006
//   *  STORE_LCL_VAR   int    V00 arg0
//   \--*  CNS_INT   int    9 $48
//
// Again this is squashed into a single block, with the SELECT node handling both cases.
//
// ------------ BB03 [009..00D) -> BB05 (always), preds={BB02} succs={BB05}
// STMT00004
//   *  NOP       void
//
// STMT00005
//   *  STORE_LCL_VAR   int    V00 arg0
//   \--*  SELECT    int
//      +--*  LT        int    $102
//      |  +--*  LCL_VAR   int    V02
//      |  \--*  CNS_INT   int    7 $46
//      +--*  CNS_INT   int    5 $47
//      +--*  CNS_INT   int    9 $48
//
// STMT00006
//   *  NOP       void
//
// ------------ BB04 [00D..010), preds={} succs={BB06}
// ------------ BB05 [00D..010), preds={} succs={BB06}
//
// Alternatively, an if conversion with an else condition may use RETURNs.
// return (x < 7) ? 5 : 9;
//
// ------------ BB03 [009..00D) -> BB05 (condition), preds={BB02} succs={BB04,BB05}
// STMT00004
//   *  JTRUE     void   $VN.Void
//   \--*  GE        int    $102
//      +--*  LCL_VAR   int    V02
//      \--*  CNS_INT   int    7 $46
//
// ------------ BB04 [00D..010), preds={BB03} succs={BB06}
// STMT00005
//   *  RETURN    int    $VN.Void
// +--*  CNS_INT   int    5 $41
//
// ------------ BB05 [00D..010), preds={BB03} succs={BB06}
// STMT00006
//   *  RETURN    int    $VN.Void
// +--*  CNS_INT   int    9 $43
//
// becomes:
//
// ------------ BB03 [009..00D) -> BB05 (always), preds={BB02} succs={BB05}
// STMT00004
//   *  NOP       void
//
// STMT00005
//   *  RETURN    int    $VN.Void
//   \--*  SELECT    int
//      +--*  LT        int    $102
//      |  +--*  LCL_VAR   int    V02
//      |  \--*  CNS_INT   int    7 $46
//      +--*  CNS_INT   int    5 $41
//      +--*  CNS_INT   int    9 $43
//
// STMT00006
//   *  NOP       void
//
// ------------ BB04 [00D..010), preds={} succs={BB06}
// ------------ BB05 [00D..010), preds={} succs={BB06}
//
bool OptIfConversionDsc::optIfConvert(int* pReachabilityBudget)
{
    if ((*pReachabilityBudget) <= 0)
    {
        return false;
    }

    if (m_jtrueBlock->StatementCount() == 0)
    {
        return false;
    }

    GenTree* jtrue = m_jtrueBlock->lastStmt()->GetRootNode();
    if (!(jtrue->OperIs(GT_JTRUE)))
    {
        return false;
    }

    if (!TryGetTransformationDsc())
    {
        return false;
    }

#ifdef DEBUG
    if (m_compiler->verbose)
    {
        JITDUMP("\nConditionally executing " FMT_BB, m_thenOperation.block->bbNum);
        if (DoElseConversion())
        {
            JITDUMP(" and " FMT_BB, m_elseOperation.block->bbNum);
        }
        JITDUMP(" inside " FMT_BB "\n", m_jtrueBlock->bbNum);
        Dump();
    }
#endif

    if (!IsProfitable(pReachabilityBudget))
    {
        return false;
    }

    // Get the select node inputs.
    var_types selectType;
    GenTree*  selectTrueInput;
    GenTree*  selectFalseInput;
    if (m_OperationType == GT_STORE_LCL_VAR)
    {
        selectFalseInput = m_thenOperation.node->AsLclVar()->Data();
        selectTrueInput  = DoElseConversion() ? m_elseOperation.node->AsLclVar()->Data() : nullptr;

        // Pick the type as the type of the local, which should always be compatible even for implicit coercions.
        selectType = genActualType(m_thenOperation.node);
    }
    else
    {
        assert(m_OperationType == GT_RETURN);
        assert(DoElseConversion());
        assert(m_thenOperation.node->TypeGet() == m_elseOperation.node->TypeGet());

        selectFalseInput = m_thenOperation.node->AsOp()->GetReturnValue();
        selectTrueInput  = m_elseOperation.node->AsOp()->GetReturnValue();
        selectType       = genActualType(m_thenOperation.node);
    }

    GenTree* condition = jtrue->gtGetOp1();
    GenTree* select = TryTransformSelectToOrdinaryOps(condition, selectTrueInput, selectFalseInput);
    if (select == nullptr)
    {
#ifdef TARGET_RISCV64
        JITDUMP("Skipping if-conversion that cannot be transformed to ordinary operations\n");
        return false;
#endif
        if (selectTrueInput == nullptr)
        {
            // Duplicate the destination of the Then store.
            assert(m_OperationType == GT_STORE_LCL_VAR && !DoElseConversion());
            GenTreeLclVar* store = m_thenOperation.node->AsLclVar();
            selectTrueInput      = m_compiler->gtNewLclVarNode(store->GetLclNum(), store->TypeGet());
        }
        // Create a select node
        select = m_compiler->gtNewConditionalNode(GT_SELECT, condition, selectTrueInput, selectFalseInput, selectType);
    }

    // Remove JTRUE statement
    jtrue->gtBashToNOP();
    m_compiler->gtSetEvalOrder(jtrue);
    m_compiler->fgSetStmtSeq(m_jtrueBlock->lastStmt());
    if (DoElseConversion())
    {
        m_elseOperation.node->gtBashToNOP();
        m_compiler->gtSetEvalOrder(m_elseOperation.node);
        m_compiler->fgSetStmtSeq(m_elseOperation.stmt);
    }

    // Use the select as the source of the Then operation.
    m_thenOperation.node->AddAllEffectsFlags(select);
    if (m_OperationType == GT_STORE_LCL_VAR)
    {
        m_thenOperation.node->AsLclVar()->Data() = select;
    }
    else
    {
        m_thenOperation.node->AsOp()->SetReturnValue(select);
    }
    m_compiler->gtSetEvalOrder(m_thenOperation.node);
    m_compiler->fgSetStmtSeq(m_thenOperation.stmt);

    // Place SELECT statement into JTRUE block and clear Then/Else blocks
    Statement* selectStmt = m_thenOperation.stmt;
    selectStmt->SetNextStmt(nullptr);
    selectStmt->SetPrevStmt(m_jtrueBlock->lastStmt());

    m_jtrueBlock->lastStmt()->SetNextStmt(selectStmt);
    m_jtrueBlock->firstStmt()->SetPrevStmt(selectStmt);
    m_thenOperation.block->bbStmtList = nullptr;
    if (HasExplicitElseBlock())
    {
        m_elseOperation.block->bbStmtList = nullptr;
    }
    
    // Update the flow graph. JTRUE block now contains the SELECT.
    //

    // Remove flow into Then/Else blocks and update their weights
    auto RemoveFlowInto = [&](BasicBlock* block) {
        m_compiler->fgRemoveAllRefPreds(block, m_jtrueBlock);
        block->bbWeight = BB_ZERO_WEIGHT;
        assert(block->bbPreds == nullptr);
    };
    RemoveFlowInto(m_jtrueBlock->GetFalseTarget());
    if (HasExplicitElseBlock())
    {
        RemoveFlowInto(m_jtrueBlock->GetTrueTarget());
    }

    // Change kind of JTRUE block and make it flow
    // directly into block where flow merges (which is null in case of GT_RETURN)
    if (m_OperationType == GT_RETURN)
    {
        m_jtrueBlock->SetKindAndTargetEdge(BBJ_RETURN);
    }
    else
    {
        FlowEdge* newEdge = HasExplicitElseBlock() ? m_compiler->fgAddRefPred(m_flowsMergeBlock, m_jtrueBlock)
                                               : m_jtrueBlock->GetTrueEdge();
        m_jtrueBlock->SetKindAndTargetEdge(BBJ_ALWAYS, newEdge);
    }

    assert(m_jtrueBlock->GetUniqueSucc() == m_flowsMergeBlock);

#ifdef DEBUG
    if (m_compiler->verbose)
    {
        JITDUMP("\nAfter if conversion\n");
        Dump();
    }
#endif

    return true;
}

struct IntConstSelectOper
{
    genTreeOps oper;
    var_types  type;
    unsigned   bitIndex;

    bool isMatched() const
    {
        return oper != GT_NONE;
    }
};

//-----------------------------------------------------------------------------
// MatchIntConstSelectValues: Matches an operation so that `trueVal` can be calculated as:
//     oper(type, falseVal, condition)
//
// Notes:
//     A non-zero bitIndex (log2(trueVal)) differentiates (condition << bitIndex) from (falseVal << condition).
//
// Return Value:
//     The matched operation (if any).
//
static IntConstSelectOper MatchIntConstSelectValues(int64_t trueVal, int64_t falseVal)
{
    if (trueVal == falseVal + 1)
        return {GT_ADD, TYP_LONG};

    if (trueVal == int64_t(int32_t(falseVal) + 1))
        return {GT_ADD, TYP_INT};

    if (falseVal == 0)
    {
        unsigned bitIndex = BitOperations::Log2((uint64_t)trueVal);
        assert(bitIndex > 0);
        if (trueVal == (int64_t(1) << bitIndex))
            return {GT_LSH, TYP_LONG, bitIndex};

        bitIndex = BitOperations::Log2((uint32_t)trueVal);
        assert(bitIndex > 0);
        if (trueVal == int64_t(int32_t(int32_t(1) << bitIndex)))
            return {GT_LSH, TYP_INT, bitIndex};
    }

    if (trueVal == falseVal << 1)
        return {GT_LSH, TYP_LONG};

    if (trueVal == int64_t(int32_t(falseVal) << 1))
        return {GT_LSH, TYP_INT};

    if (trueVal == falseVal >> 1)
        return {GT_RSH, TYP_LONG};

    if (trueVal == int64_t(int32_t(falseVal) >> 1))
        return {GT_RSH, TYP_INT};

    if (trueVal == int64_t(uint64_t(falseVal) >> 1))
        return {GT_RSZ, TYP_LONG};

    if (trueVal == int64_t(uint32_t(falseVal) >> 1))
        return {GT_RSZ, TYP_INT};

    return {GT_NONE};
}

//-----------------------------------------------------------------------------
// TryTransformSelectOperOrLocal: Try to trasform "condition ? oper(lcl, (-)1) : lcl" into "oper(')(lcl, condition)"
//
// Arguments:
//     trueInput  - expression to be evaluated when condition is true
//     falseInput - expression to be evaluated when condition is false
//
// Return Value:
//     The transformed expression, or null if no transformation took place
//
GenTree* OptIfConversionDsc::TryTransformSelectOperOrLocal(GenTree* condition, GenTree* trueInput, GenTree* falseInput)
{
    GenTree* oper = trueInput;
    GenTree* lcl  = falseInput;

    bool isCondReversed = !lcl->OperIsAnyLocal();
    if (isCondReversed)
        std::swap(oper, lcl);

    if (lcl->OperIsAnyLocal() && (oper->OperIs(GT_ADD, GT_OR, GT_XOR) || oper->OperIsShift()))
    {
        GenTree* lcl2 = oper->gtGetOp1();
        GenTree* one  = oper->gtGetOp2();
        if (oper->OperIsCommutative() && !one->IsIntegralConst())
            std::swap(lcl2, one);

        bool isDecrement = oper->OperIs(GT_ADD) && one->IsIntegralConst(-1);
        if (one->IsIntegralConst(1) || isDecrement)
        {
            unsigned lclNum = lcl->AsLclVarCommon()->GetLclNum();
            if (lcl2->OperIs(GT_LCL_VAR) && (lcl2->AsLclVar()->GetLclNum() == lclNum))
            {
                oper->AsOp()->gtOp1 = lcl2;
                oper->AsOp()->gtOp2 = isCondReversed ? m_compiler->gtReverseCond(condition) : condition;
                if (isDecrement)
                    oper->ChangeOper(GT_SUB);

                oper->gtFlags |= condition->gtFlags & GTF_ALL_EFFECT;
                return oper;
            }
        }
    }
    return nullptr;
}

//-----------------------------------------------------------------------------
// TryTransformSelectOperOrZero: Try to trasform "condition ? oper(1, expr) : 0" into "oper(condition, expr)"
//
// Arguments:
//     trueInput  - expression to be evaluated when condition is true
//     falseInput - expression to be evaluated when condition is false
//
// Return Value:
//     The transformed expression, or null if no transformation took place
//
GenTree* OptIfConversionDsc::TryTransformSelectOperOrZero(GenTree* condition, GenTree* trueInput, GenTree* falseInput)
{
    GenTree* oper = trueInput;
    GenTree* zero = falseInput;

    bool isCondReversed = !zero->IsIntegralConst();
    if (isCondReversed)
        std::swap(oper, zero);

    if (zero->IsIntegralConst(0) && oper->OperIs(GT_AND, GT_LSH))
    {
        GenTree* one  = oper->gtGetOp1();
        GenTree* expr = oper->gtGetOp2();
        if (oper->OperIsCommutative() && !one->IsIntegralConst())
            std::swap(one, expr);

        if (one->IsIntegralConst(1))
        {
            oper->AsOp()->gtOp1 = isCondReversed ? m_compiler->gtReverseCond(condition) : condition;
            oper->AsOp()->gtOp2 = expr;

            oper->gtFlags |= condition->gtFlags & GTF_ALL_EFFECT;
            return oper;
        }
    }
    return nullptr;
}

//-----------------------------------------------------------------------------
// TryTransformSelectToOrdinaryOps: Try transforming the identified if-else expressions to a single expression
//
// This is meant mostly for RISC-V where the condition (1 or 0) is stored in a regular general-purpose register
// which can be fed as an argument to standard operations, e.g.
//     * (condition ? 6 : 5) becomes (5 + condition)
//     * (condition ? -25 : -13) becomes (-25 >> condition)
//     * if (condition) a++; becomes (a + condition)
//     * (condition ? 1 << a : 0) becomes (condition << a)
//
// Arguments:
//     trueInput  - expression to be evaluated when condition is true, or null if there is no else expression
//     falseInput - expression to be evaluated when condition is false
//
// Return Value:
//     The transformed single expression equivalent to the if-else expressions, or null if no transformation took place
//
GenTree* OptIfConversionDsc::TryTransformSelectToOrdinaryOps(GenTree* condition, GenTree* trueInput, GenTree* falseInput)
{
    assert(falseInput != nullptr);

    if ((trueInput != nullptr && trueInput->IsIntegralConst()) && falseInput->IsIntegralConst())
    {
        int64_t trueVal  = trueInput->AsIntConCommon()->IntegralValue();
        int64_t falseVal = falseInput->AsIntConCommon()->IntegralValue();
        if (trueInput->TypeIs(TYP_INT) && falseInput->TypeIs(TYP_INT))
        {
            if (trueVal == 1 && falseVal == 0)
            {
                // compare ? true : false  -->  compare
                return condition;
            }
            else if (trueVal == 0 && falseVal == 1)
            {
                // compare ? false : true  -->  reversed_compare
                return m_compiler->gtReverseCond(condition);
            }
        }
#ifdef TARGET_RISCV64
        if (varTypeIsIntegral(trueInput) && varTypeIsIntegral(falseInput) && (trueVal != falseVal))
        {
            bool               isCondReversed = false;
            IntConstSelectOper selectOper     = MatchIntConstSelectValues(trueVal, falseVal);
            if (!selectOper.isMatched())
            {
                isCondReversed = true;
                selectOper     = MatchIntConstSelectValues(falseVal, trueVal);
            }
            if (selectOper.isMatched())
            {
                GenTree* left  = isCondReversed ? trueInput : falseInput;
                GenTree* right = isCondReversed ? m_compiler->gtReverseCond(condition) : condition;
                if (selectOper.bitIndex > 0)
                {
                    assert(selectOper.oper == GT_LSH);
                    left->AsIntConCommon()->SetIntegralValue(selectOper.bitIndex);
                    std::swap(left, right);
                }
                return m_compiler->gtNewOperNode(selectOper.oper, selectOper.type, left, right);
            }
        }
#endif // TARGET_RISCV64
    }
#ifdef TARGET_RISCV64
    else
    {
        if (trueInput == nullptr)
        {
            assert(m_mainOper == GT_STORE_LCL_VAR && !m_doElseConversion);
            trueInput = m_thenOperation.node;
        }

        GenTree* transformed = TryTransformSelectOperOrLocal(condition, trueInput, falseInput);
        if (transformed != nullptr)
            return transformed;

        transformed = TryTransformSelectOperOrZero(condition, trueInput, falseInput);
        if (transformed != nullptr)
            return transformed;
    }
#endif // TARGET_RISCV64
    return nullptr;
}

//-----------------------------------------------------------------------------
// optIfConversion: If conversion
//
// Returns:
//   suitable phase status
//
PhaseStatus Compiler::optIfConversion()
{
    if (!opts.OptimizationEnabled())
    {
        return PhaseStatus::MODIFIED_NOTHING;
    }

#if defined(DEBUG)
    if (JitConfig.JitDoIfConversion() == 0)
    {
        return PhaseStatus::MODIFIED_NOTHING;
    }
#endif

    bool madeChanges = false;

    // This phase does not respect SSA: local stores are deleted/moved.
    assert(!fgSsaValid);
    optReachableBitVecTraits = nullptr;

#if defined(TARGET_ARM64) || defined(TARGET_XARCH) || defined(TARGET_RISCV64)
    // Reverse iterate through the blocks.
    BasicBlock* block = fgLastBB;

    // Budget for optReachability - to avoid spending too much time detecting loops in large methods.
    int reachabilityBudget = 20000;
    while (block != nullptr)
    {
        OptIfConversionDsc optIfConversionDsc(this, block);
        madeChanges |= optIfConversionDsc.optIfConvert(&reachabilityBudget);
        block = block->Prev();
    }
#endif

    return madeChanges ? PhaseStatus::MODIFIED_EVERYTHING : PhaseStatus::MODIFIED_NOTHING;
}
