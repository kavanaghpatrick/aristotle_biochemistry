#!/bin/bash
# Query Gemini for validation of geometric reachability plan.
# Focus: Scientific soundness, publication viability, alternative approaches.

PLAN=$(cat docs/geometric_breakthrough_plan.md)

gemini -p "You are a computational chemist and structural biologist reviewing a formal verification plan for drug safety. Please provide critical scientific feedback.

# PLAN TO REVIEW:
$PLAN

# SPECIFIC QUESTIONS:

1. **Geometric vs Pharmacophore**: Will geometric proofs catch MORE molecules than the pharmacophore feature-absence approach? Or is the coverage actually lower?

2. **Macrolide Hypothesis**: The plan hypothesizes azithromycin/erythromycin will fail volume exclusion (MW 749/734 Da). Is this reasonable? What's your estimate of their molecular volumes?

3. **Rigidity Assumption**: Is treating molecules as rigid conformers a fundamental scientific flaw? Can you give examples where this would fail?

4. **Missing Mechanisms**: Are there known hERG binding modes that would bypass geometric constraints (e.g., allosteric binding, dynamic pocket expansion)?

5. **Publication Viability**: Is this approach novel enough for a high-impact journal (Nature Methods, PLOS Comp Bio)? Or is it incremental?

6. **Comparison to QSAR**: How does this compare to ML-based QSAR models (80-90% accuracy, full coverage)? What's the value proposition?

7. **Generalization**: The plan claims this generalizes to ANY target with crystal structure. True? Or are there target-specific limitations?

8. **Alternative Approaches**: Should we pursue multi-conformer analysis instead? Or focus on a different target than hERG?

# YOUR TASK:
- Evaluate scientific soundness and rigor
- Identify potential false assumptions
- Assess novelty and impact
- Compare to existing methods (docking, QSAR, etc.)
- Rate publication potential (1-10) and explain

Be CRITICAL. Would you approve this for your PhD student? Would you review this positively?

Output your response to: research/gemini_geometric_validation.md
" > research/gemini_geometric_validation.md

echo "✅ Gemini validation complete!"
echo "📄 Saved to: research/gemini_geometric_validation.md"
echo ""
echo "================================================================================"
echo "GEMINI FEEDBACK:"
echo "================================================================================"
cat research/gemini_geometric_validation.md
