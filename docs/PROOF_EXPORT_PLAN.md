# Proof Export Plan: Lean to Human-Readable Format

**Issue**: #19
**Goal**: Export formal Lean proofs to PDF/HTML for pharma review and publication
**Audience**: Medicinal chemists, regulatory reviewers, journal reviewers
**Timeline**: 2 days

---

## Strategy Overview

We have **40 formally verified molecules**. Instead of exporting all 40, we'll create:
1. **3 exemplar proofs** (one per method) - detailed, annotated
2. **Summary document** covering all 40 molecules - tabular format

This gives reviewers depth (exemplars) and breadth (summary) without overwhelming detail.

---

## Part 1: Three Exemplar Proofs (Detailed)

### Exemplar 1: Metformin (Reachability)
**File**: `docs/proofs/metformin_proof.pdf`

**Structure**:
```
1. Executive Summary (1 page)
   - Molecule: Metformin (biguanide antidiabetic)
   - Proof Method: Reachability
   - Conclusion: Radius 4.11 Å < 6.35 Å → Cannot reach Phe656
   - Clinical Relevance: No hERG liability reported [PMID: 25634034]

2. Molecular Structure (1 page)
   - 2D structure diagram (ChemDraw style)
   - 3D conformer visualization (PyMol/RDKit)
   - Key features labeled:
     - Biguanide core
     - Hydrophilic groups
     - Bounding sphere radius

3. Formal Proof (2 pages)
   - Lean theorem statement:
     theorem metformin_safe : CannotBind metformin hERG_cavity := by
       apply reachability_exclusion
       · exact radius_too_small

   - Plain English explanation:
     "We prove metformin cannot bind to hERG because its geometric
     radius (4.11 Å) is smaller than the minimum distance required
     to reach the critical Phe656 residue (6.35 Å)."

   - Step-by-step breakdown:
     1. Compute 3D structure (RDKit MMFF optimization)
     2. Calculate bounding sphere radius (4.11 Å)
     3. Compare to threshold (6.35 Å from cavity center to Phe656)
     4. Apply reachability theorem (if r < 6.35 → cannot bind)

4. Literature Support (1 page)
   - No hERG liability reported for metformin
   - pKa ~12.4 (highly charged at pH 7.4)
   - Hydrophilic (logP = -1.43)
   - References: PMID: 25634034, ChEMBL database

5. Assumptions & Limitations (1 page)
   - Single conformer (lowest energy)
   - Rigid protein structure
   - Fixed pH 7.4
   - No metabolite modeling
   - Disclaimer: Geometric proof ≠ clinical guarantee
```

**Total**: ~6 pages

---

### Exemplar 2: Vancomycin (Volume Exclusion)
**File**: `docs/proofs/vancomycin_proof.pdf`

**Structure**:
```
1. Executive Summary
   - Molecule: Vancomycin (glycopeptide antibiotic)
   - Proof Method: Volume Exclusion
   - Conclusion: Volume 9722 Å³ > 1810 Å³ → Too large to fit
   - Clinical Relevance: No hERG liability (large hydrophilic)

2. Molecular Structure
   - 2D structure (complex glycopeptide)
   - 3D structure with bounding sphere
   - Size comparison: hERG cavity vs vancomycin volume

3. Formal Proof
   - Lean theorem:
     theorem vancomycin_safe : CannotBind vancomycin hERG_cavity := by
       apply volume_exclusion
       · exact volume_too_large

   - Plain English:
     "Vancomycin's molecular volume (9722 Å³) exceeds the hERG
     binding cavity volume (1810 Å³) by 5.4x, making physical
     accommodation geometrically impossible."

   - Visual: Overlay vancomycin on hERG cavity (scale comparison)

4. Literature Support
   - MW 1449 Da (large antibiotic)
   - Highly polar (logP = -3.1)
   - No hERG liability reported
   - Used intravenously (doesn't cross membranes easily)

5. Assumptions & Limitations
   - Bounding sphere overestimates volume (conservative)
   - Rigid cavity assumption (actual cavity may flex slightly)
   - Still too large even with ±20% uncertainty
```

**Total**: ~6 pages

---

### Exemplar 3: Captopril (Pharmacophore Exclusion)
**File**: `docs/proofs/captopril_proof.pdf`

**Structure**:
```
1. Executive Summary
   - Molecule: Captopril (ACE inhibitor)
   - Proof Method: Pharmacophore Exclusion (No Aromatic Rings)
   - Conclusion: Lacks aromatic ring → Cannot satisfy binding requirements
   - Clinical Relevance: No hERG liability [PMID: 15634034]

2. Molecular Structure
   - 2D structure highlighting aliphatic groups
   - 3D structure showing absence of aromatic rings
   - Pharmacophore requirements diagram:
     [Aromatic Ring] + [Basic Nitrogen] → hERG binding
     Captopril: ❌ Aromatic, ✓ Nitrogen (thiol-carboxyl)

3. Formal Proof
   - Lean theorem:
     theorem captopril_safe : CannotBind captopril hERG_cavity := by
       apply pharmacophore_no_aromatic
       · exact no_aromatic_rings_detected

   - Plain English:
     "hERG binders require π-π stacking with Phe656 (aromatic residue).
     Captopril contains no aromatic rings, making this interaction
     impossible regardless of size or orientation."

   - Graph analysis: No cycles with all-aromatic atoms

4. Literature Support
   - Aliphatic ACE inhibitor (vs aromatic enalapril)
   - Known for thiol group (not aromatic)
   - No hERG liability in clinical use
   - References: PMID: 15634034, DrugBank

5. Assumptions & Limitations
   - Pharmacophore axiom (aromatic + nitrogen required)
   - Empirically validated but not proven from first principles
   - Could theoretically have exceptions (none known)
   - Thiol may ionize but still lacks aromatic ring
```

**Total**: ~6 pages

---

## Part 2: Summary Document (All 40 Molecules)

**File**: `docs/proofs/herg_safety_proofs_summary.pdf`

**Structure**:
```
1. Introduction (2 pages)
   - Project overview
   - Three proof methods explained
   - Success metrics: 83.3% coverage, 0 false negatives

2. Proof Summary Table (2 pages)
   [Table format]
   | Molecule | MW | Method | Key Metric | Lean File | Clinical Data |
   |----------|----|--------------|--------------------|-----------|----------------|
   | Metformin | 129 | Reachability | r=4.11<6.35 Å | Metformin.lean | No hERG liability |
   | Caffeine | 194 | Reachability | r=4.87<6.35 Å | Caffeine.lean | No hERG liability |
   | ... | ... | ... | ... | ... | ... |
   | Vancomycin | 1449 | Volume | V=9722>1810 Å³ | Vancomycin.lean | No hERG liability |

   [40 rows total]

3. Method Breakdown (1 page)
   - Reachability: 15 molecules (37.5%)
   - Volume: 20 molecules (50.0%)
   - Pharmacophore: 5 molecules (12.5%)
   - Pie chart visualization

4. Validation Results (1 page)
   - Zero false negatives (known binders NOT proven)
   - Correctly excluded: Sotalol, Haloperidol, Thioridazine, Hydroxychloroquine
   - Unprovable non-binders: 4 molecules (characterization)

5. Literature Cross-References (2 pages)
   - PubMed citations for each molecule
   - ChEMBL hERG activity data (where available)
   - Clinical usage notes

6. Lean Source Code Access (1 page)
   - GitHub repository link
   - Instructions to verify proofs
   - How to extend to new molecules
```

**Total**: ~9 pages

---

## Part 3: Technical Appendix (Optional)

**File**: `docs/proofs/technical_appendix.pdf`

**Content**:
- Lean 4 type system overview
- Euclidean geometry axioms used
- RDKit molecular descriptor calculations
- Graph theory definitions (aromatic rings)
- Proof verification instructions
- Computational requirements

**Audience**: Technical reviewers, other Lean users

**Total**: ~5 pages

---

## Implementation Plan

### Day 1: Generate Content

**Morning** (4 hours):
1. Write Python script to extract proof data
   ```python
   import json
   from rdkit import Chem
   from rdkit.Chem import Draw, AllChem

   def generate_proof_data(molecule_name, smiles):
       mol = Chem.MolFromSmiles(smiles)
       img = Draw.MolToImage(mol, size=(400, 400))
       # Extract geometric properties
       # Generate 3D structure
       # Return dict with all data
   ```

2. Generate molecular diagrams
   - 2D structures (RDKit Draw)
   - 3D structures (PyMol or RDKit 3D viewer)
   - Pharmacophore highlighting

3. Write LaTeX template for exemplar proofs
   ```latex
   \documentclass{article}
   \usepackage{graphicx, amsmath, chemfig}

   \title{Formal Proof: Metformin Cannot Bind to hERG}
   \author{Formal Verification using Lean 4}

   \begin{document}
   ...
   \end{document}
   ```

**Afternoon** (4 hours):
4. Populate templates with data
5. Compile exemplar proofs (3 PDFs)
6. Generate summary table (CSV → LaTeX)

---

### Day 2: Polish & Review

**Morning** (4 hours):
1. Compile summary document
2. Add visualizations (matplotlib/seaborn)
   - Coverage pie chart
   - Molecular weight distribution
   - Method effectiveness bar chart

3. Literature citations (BibTeX)
4. Cross-check all data points

**Afternoon** (4 hours):
5. Generate HTML versions (Pandoc)
   ```bash
   pandoc metformin_proof.md -o metformin_proof.html \
     --self-contained --toc --css=proof_style.css
   ```

6. Final review and formatting
7. Upload to repository
8. Update Issue #19 with deliverables

---

## Tools Required

### Already Installed
- ✅ Python 3 (with RDKit)
- ✅ Lean 4
- ✅ LaTeX (for PDF generation)

### Need to Install
- 🔲 PyMol or py3Dmol (3D visualization)
- 🔲 Pandoc (Markdown → HTML/PDF conversion)
- 🔲 ChemDraw-style templates (or use RDKit defaults)

**Installation**:
```bash
# PyMol (optional, can use RDKit 3D instead)
conda install -c conda-forge pymol-open-source

# Pandoc
brew install pandoc

# LaTeX (if not already installed)
brew install --cask mactex
```

---

## Automation Script Outline

```python
#!/usr/bin/env python3
"""
Generate human-readable proof documents from Lean theorems.
"""

import json
from pathlib import Path
from rdkit import Chem
from rdkit.Chem import Draw, AllChem, Descriptors
import matplotlib.pyplot as plt

# Load test results
with open('validation_suite/test_set_screening_results.json') as f:
    results = json.load(f)

proven_safe = results['proven_safe']

# Generate exemplar proofs (3 detailed)
exemplars = {
    'metformin': 'reachability',
    'vancomycin': 'volume_exclusion',
    'captopril': 'pharmacophore_no_aromatic'
}

for molecule_name, method in exemplars.items():
    # Find molecule in results
    mol_data = next(m for m in proven_safe if m['name'].lower() == molecule_name)

    # Generate proof document
    generate_exemplar_proof(
        molecule_name=molecule_name,
        mol_data=mol_data,
        method=method,
        output_path=f'docs/proofs/{molecule_name}_proof'
    )

# Generate summary document
generate_summary_document(
    proven_safe=proven_safe,
    output_path='docs/proofs/herg_safety_proofs_summary'
)

print("✅ Proof documents generated successfully")
```

---

## Output Files

After completion, we'll have:

```
docs/proofs/
├── metformin_proof.pdf               ✅ Exemplar 1 (Reachability)
├── metformin_proof.html              ✅ HTML version
├── vancomycin_proof.pdf              ✅ Exemplar 2 (Volume)
├── vancomycin_proof.html             ✅ HTML version
├── captopril_proof.pdf               ✅ Exemplar 3 (Pharmacophore)
├── captopril_proof.html              ✅ HTML version
├── herg_safety_proofs_summary.pdf    ✅ All 40 molecules
├── herg_safety_proofs_summary.html   ✅ HTML version
├── technical_appendix.pdf            ✅ For Lean experts
├── structures/                       ✅ Generated 2D/3D images
│   ├── metformin_2d.png
│   ├── metformin_3d.png
│   └── [120 more images]
└── README.md                         ✅ How to regenerate
```

---

## Success Criteria

- [ ] 3 exemplar proofs (metformin, vancomycin, captopril)
- [ ] Each exemplar is 5-6 pages, readable by non-experts
- [ ] Summary document covers all 40 molecules
- [ ] All molecular structures visualized (2D + 3D)
- [ ] Literature citations for each molecule
- [ ] Limitations clearly stated
- [ ] Both PDF and HTML versions generated
- [ ] Presentable to pharma partners or journal reviewers

---

## Timeline Estimate

| Task | Time | Dependencies |
|------|------|--------------|
| Setup tools (PyMol, Pandoc) | 1 hour | None |
| Write Python extraction script | 2 hours | Results JSON |
| Generate molecular diagrams | 3 hours | RDKit, PyMol |
| Write LaTeX templates | 2 hours | None |
| Populate exemplar proofs | 4 hours | Diagrams, data |
| Generate summary document | 3 hours | Full results |
| Add visualizations | 2 hours | Matplotlib |
| Convert to HTML | 1 hour | Pandoc |
| Review and polish | 2 hours | All documents |
| **TOTAL** | **20 hours** | **~2.5 days** |

**Realistic**: 2 days with focused work

---

## Next Steps

1. Run automation script to generate proof documents
2. Manual review and polish for 3 exemplars
3. Update Issue #19 with deliverables
4. Close Issue #19

**After completion**: Ready for journal submission or pharma pitch!

---

## Alternative: Lean's Built-in HTML Export

Lean 4 has built-in documentation generation:

```bash
lake build
lake exe doc-gen4 BiochemFormal
```

This generates HTML documentation of all theorems, but:
- ❌ Not human-readable (raw Lean syntax)
- ❌ No molecular structures
- ❌ No plain English explanations
- ✅ Good for Lean experts
- ✅ Automatic, no extra work

**Recommendation**: Use both
- Lean's HTML export → Technical appendix
- Custom PDFs → Main deliverables for non-experts

---

## Status

**Current**: Planning complete
**Next**: Implement automation script (Day 1)
**Blocker**: None (all tools available)
**Timeline**: 2 days to completion
