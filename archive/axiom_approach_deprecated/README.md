# Deprecated: Axiom-Based Pharmacophore Approach

**Date Deprecated**: 2025-12-11
**Reason**: Not a true breakthrough - equivalent to pattern matching

---

## What Was This Approach?

Encoded literature-known pharmacophore rules as Lean axioms:
```lean
axiom necessary_features (m : Molecule) :
  BindsHERG m → (has_cationic ∧ has_aromatic ∧ has_hydrophobe)
```

Then proved molecules safe if they lacked features:
```lean
theorem aspirin_safe : ¬BindsHERG aspirin := by
  apply no_cationic_is_safe
  rfl
```

---

## Why Deprecated?

1. **Not a Breakthrough**: Just encoding known rules, not discovering new knowledge
2. **False Negatives**: 28.6% (macrolides bound despite lacking aromatic features)
3. **Axiom Limitation**: Aristotle refused to work with custom axioms
4. **Equivalent to Pattern Matching**: Could be replaced with `if 'N' not in smiles: print("safe")`

---

## What Replaced It?

**Geometric Reachability Approach** (see `docs/geometric_breakthrough_plan.md`):
- Formalize actual hERG structure from PDB
- Prove geometric impossibility (steric clash, volume exclusion)
- Axiom-free (built on Mathlib geometry)
- TRUE breakthrough (first-ever formal proofs for protein-ligand binding)

---

## Files Archived

- `Core.lean` - Original complex axiom formalization
- `CoreSimple.lean` - Simplified axiom approach
- `MetforminAspirin.lean` - Axiom-based safety proofs
- `Terfenadine.lean` - Terfenadine axiom proof
- `TerfenadineSimple.lean` - Aristotle test file
- `comprehensive_extraction.py` - Feature-absence classification
- `batch_extract_features.py` - Batch axiom-based processing
- `constraint_validation_findings.md` - Distance constraint failure analysis
- `comprehensive_drug_dataset.json` - 50 drug dataset
- `comprehensive_features/` - Feature extraction results

---

## Lessons Learned

1. **Validate assumptions early**: Distance constraints failed 97% test
2. **Axioms aren't breakthroughs**: Encoding literature ≠ discovering knowledge
3. **Simplicity ≠ Correctness**: Simple axiom had 28.6% false negatives
4. **First principles > empirical rules**: Geometric proofs more rigorous

---

## Historical Value

This work was NOT wasted:
- ✅ Validated Aristotle can prove biochemistry facts (7/7 test theorems)
- ✅ Built RDKit extraction pipeline (reusable for geometric approach)
- ✅ Learned hERG binding is complex (multiple mechanisms)
- ✅ Discovered feature-absence has false negatives (macrolides)
- ✅ Proved need for geometric formalization

**This failure led to the breakthrough insight.**

---

**See**: `docs/ultrathink_session_summary.md` for full history
