# Deep Research Prompt: hERG Toxicity Formal Verification

## Context
We're building the FIRST formal verification system for drug discovery using Lean 4 + Aristotle AI. hERG cardiac toxicity is the #1 most expensive problem ($500M+ per failure, most common Phase III withdrawal reason).

## Your Task
Research and propose the SIMPLEST, most practical approach to formally verify that a drug molecule CANNOT bind to the hERG potassium channel.

## Key Questions

### 1. Scientific Understanding
- What makes hERG binding hard to predict?
- What structural features cause hERG binding?
- What data is available? (Cryo-EM structures, IC50 databases, failed drugs)
- Can we prove IMPOSSIBILITY rather than predict affinity?

### 2. Formal Verification Approach
- What mathematical properties can we prove?
- Geometric exclusion (molecule too large/wrong shape)?
- Electrostatic incompatibility (wrong charges)?
- Thermodynamic impossibility (ΔG > 0)?
- Which is SIMPLEST to formalize in Lean 4?

### 3. Lean 4 Formalization
- What's the minimal model needed?
- How detailed must molecular structure be? (Atoms? Pharmacophore? SMILES?)
- Can we use discrete geometry or need continuous?
- What theorems from Mathlib can we leverage?

### 4. Aristotle Feasibility
- Can Aristotle prove these theorems automatically?
- Or do we need human-guided proofs?
- What's a realistic first milestone? (1 molecule? 1 property? 1 drug class?)

### 5. Business Value
- What's the MINIMUM viable proof that pharma would value?
- "Molecule X cannot bind hERG" for ONE drug?
- "All molecules with property P avoid hERG" for a class?
- What level of confidence? (Proof vs probabilistic guarantee)

### 6. Implementation Strategy
- Start with what? (Literature review? One failed drug? Geometric toy model?)
- What's the 80/20? (20% effort, 80% value)
- What can we prove in 2-4 weeks realistically?

## Output Requirements

Provide:
1. **Scientific Summary** (200 words): Why hERG is hard
2. **Formal Approach** (300 words): What to prove and why it's simplest
3. **Lean Formalization Sketch** (code or pseudocode): Key types and theorems
4. **Feasibility Assessment** (100 words): Can Aristotle handle this?
5. **MVP Definition** (100 words): Minimum proof for pharma value
6. **Implementation Plan** (5 steps): From research to working proof

## Simplicity Principle
- Prefer discrete over continuous
- Prefer geometric over thermodynamic
- Prefer impossibility proofs over predictions
- Prefer existing data over new experiments
- Prefer 1 strong example over 10 weak ones

Be brutally honest about feasibility. We want REAL proofs, not hand-waving.
