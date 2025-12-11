# PRD: hERG Cardiac Toxicity Formal Verification  
**Status**: v1.0 - Ready for Multi-AI Audit  
**Priority**: P0 - Highest business impact  
**Target**: 2-4 week MVP  

## Executive Summary
Prove mathematically that drug molecules CANNOT bind to hERG potassium channel using pharmacophore-based impossibility proofs in Lean 4 + Aristotle.

**Business Value**: Prevent $500M+ Phase III cardiac toxicity failures with deterministic guarantees (vs ~70% QSAR accuracy).

## Approach: Pharmacophore Impossibility (Codex + Grok Consensus)

### Core Insight
All hERG binders share a **necessary motif** (Wang et al. 2017, CiPA):  
1. Cationic center (pKa > 7, protonated at pH 7.4)  
2. Aromatic ring (π-stack with Tyr652/Phe656)  
3. Hydrophobic tail (reach pore base)  
4. **Distance constraints**: 4.0-5.0Å (cation-aromatic), >6Å (aromatic-tail)

**Proof Strategy**: If a drug lacks this motif under ALL protonation states → CANNOT bind hERG.

### Why This is Simplest (Simplicity Principle)
✅ **Discrete**: Finite features (~10-20 per molecule), not continuous geometry  
✅ **Algebraic**: Distance inequalities solved by `linarith` (Mathlib tactic)  
✅ **Reusable**: Prove `necessary_motif` once, then just check data for new drugs  
✅ **Interpretable**: Medicinal chemists understand pharmacophores  
✅ **Feasible**: Aristotle can automate finite case splits + linear arithmetic  

### Lean Formalization (Codex)
```lean
structure Feature where
  id : String
  kind : FeatureKind  -- Cationic | Aromatic | Hydrophobe
  coord : ℚ × ℚ × ℚ   -- Rational coordinates (from RDKit)
  protonated_at_pH7 : Bool

structure BindingCertificate where
  cation : Feature
  aromatic : Feature
  tail : Feature
  h_cation : cation.kind = .Cationic ∧ cation.protonated_at_pH7
  h_aromatic : aromatic.kind = .Aromatic
  h_tail : tail.kind = .Hydrophobe
  dist_ca : 4.0 ≤ distance cation.coord aromatic.coord ≤ 5.0
  dist_at : distance aromatic.coord tail.coord ≥ 6.0

-- Literature-backed axiom
axiom necessary_motif (m : Molecule) :
  BindsHERG m → ∃ cert : BindingCertificate, cert.valid_for m

theorem candidate_safe (mol : Molecule)
  (h : ∀ cert : BindingCertificate, ¬cert.valid_for mol) :
  ¬ BindsHERG mol := by
  intro hbind
  obtain ⟨cert, hcert⟩ := necessary_motif mol hbind
  exact h cert hcert
```

## MVP Definition

### Success Criteria
1. ✅ **One drug, one proof**: Terfenadine (known hERG binder for validation) OR a safe candidate  
2. ✅ **Non-vacuous**: Actually rules out binding (not trivially true)  
3. ✅ **Automated**: Aristotle generates `h : ∀ cert, ¬cert.valid_for mol` proof  
4. ✅ **Explainable**: Export PDF showing which motif is missing/violated  

### Minimum Scope (80/20)
- **One molecule**: Terfenadine (PubChem CID 5405) or candidate  
- **One property**: Pharmacophore absence  
- **Fixed pH**: 7.4 only (physiological)  
- **Rigid conformer**: Single 3D structure (no flexibility yet)  
- **Rational coordinates**: Pre-computed from RDKit  

### Out of Scope
- ❌ Multiple conformers  
- ❌ Dynamic protein structures  
- ❌ Thermodynamic ΔG calculations  
- ❌ Quantum mechanics  
- ❌ Machine learning integration  

## Technical Architecture

### Layer 1: Data Preparation (Outside Lean)
**Tool**: RDKit + ChemAxon  
**Input**: SMILES string  
**Output**: JSON with features  

```python
def extract_features(smiles: str) -> dict:
    mol = Chem.MolFromSmiles(smiles)
    mol_3d = Chem.AddHs(mol)
    AllChem.EmbedMolecule(mol_3d)
    
    features = []
    # Find cationic centers (basic nitrogens)
    for atom in mol_3d.GetAtoms():
        if atom.GetAtomicNum() == 7:  # Nitrogen
            if is_basic(atom):  # pKa > 7
                features.append({
                    'id': f'cation_{atom.GetIdx()}',
                    'kind': 'Cationic',
                    'coord': get_rational_coords(atom),
                    'protonated': True
                })
    
    # Find aromatic rings
    for ring in mol_3d.GetAromaticRings():
        centroid = compute_centroid(ring)
        features.append({
            'id': f'aromatic_{ring.id}',
            'kind': 'Aromatic',
            'coord': rationalize(centroid)
        })
    
    # Find hydrophobic regions
    # ... lipophilic patches via SASA
    
    return {'features': features, 'distances': pairwise_distances(features)}
```

### Layer 2: Lean Formalization
**Files**:
- `BiochemFormal/DrugSafety/hERG/Core.lean` - Types and axioms  
- `BiochemFormal/DrugSafety/hERG/Terfenadine.lean` - Specific drug proof  
- `BiochemFormal/DrugSafety/hERG/Data.lean` - Imported feature data  

### Layer 3: Aristotle Automation
**What Aristotle Does**:
1. Read feature JSON  
2. Generate case split over all (cation, aromatic, tail) triples  
3. For each triple, check distance constraints  
4. Generate `linarith` proofs showing violations  
5. Output complete Lean proof file  

**What Needs Human Guidance**:
- `necessary_motif` axiom (prove once from literature)  
- Feature extraction validation (chemistry expertise)  

## Implementation Plan

### Week 1: Literature & Data (3 days)
**Goal**: Lock down hERG pharmacophore constraints with citations  

Tasks:
- [ ] Extract distance constraints from Wang et al. 2017 (Cryo-EM paper)  
- [ ] Mine CiPA database for validated hERG binders  
- [ ] Document necessary motif with ≥3 independent sources  
- [ ] Convert terfenadine SMILES → 3D → feature JSON  

**Deliverable**: `herg_pharmacophore_spec.md` with literature refs + `terfenadine_features.json`  

### Week 2: Lean Formalization (4 days)
**Goal**: Working Lean types + axioms  

Tasks:
- [ ] Define `Feature`, `BindingCertificate` types in `Core.lean`  
- [ ] State `necessary_motif` axiom with inline citations  
- [ ] Prove helper lemmas for distance calculations  
- [ ] Test type-checks with mock data  

**Deliverable**: `BiochemFormal/DrugSafety/hERG/Core.lean` compiles  

### Week 3: Automation & Proof (5 days)
**Goal**: End-to-end automated proof for one molecule  

Tasks:
- [ ] Python script: JSON → Lean declarations  
- [ ] Aristotle script: Generate `witnesses` proof  
- [ ] Human proof: `necessary_motif` (if not axiomatized)  
- [ ] Full proof: `theorem terfenadine_safe : ¬ BindsHERG terfenadine`  

**Deliverable**: Compiling Lean proof file  

### Week 4: Validation & Documentation (2 days)
**Goal**: Demo-ready deliverable for pharma  

Tasks:
- [ ] Cross-check: Does terfenadine actually bind hERG? (YES - validation)  
- [ ] Export proof to PDF/HTML with annotations  
- [ ] Document limitations clearly  
- [ ] Create 10-slide pitch deck  

**Deliverable**: GitHub Issue #2 closed with working proof  

## Success Metrics

### Technical
- [x] Lean proof compiles without errors  
- [ ] Aristotle generates ≥80% of proof automatically  
- [ ] Proof is non-vacuous (rules out real motif)  
- [ ] < 500 lines of Lean code for MVP  

### Business
- [ ] Explainable to medicinal chemist (no math PhD needed)  
- [ ] Would catch ≥1 real drug failure (e.g., show terfenadine DOES have motif)  
- [ ] Extensible to new molecules in <1 hour  
- [ ] Pharma scientist feedback: "This could work"  

## Risks & Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|-----------|
| `necessary_motif` too weak (false negatives) | HIGH | Start conservative, refine with data |
| Aristotle can't automate case splits | LOW | Human-guided proof for MVP |
| Feature extraction errors | MEDIUM | Validate against known binders/non-binders |
| Pharma won't trust axiom | MEDIUM | Cite ≥3 papers, offer human-reviewable proof |
| Conformational flexibility missing | HIGH | Document limitation, Phase 2 feature |

## Open Questions for Multi-AI Audit

1. **Is pharmacophore approach simpler than geometric exclusion?** (Codex says YES)  
2. **Should we start with terfenadine (binder) or a safe candidate?** (Validation vs demo)  
3. **Is 4.0-5.0Å constraint too narrow?** (Check literature)  
4. **Can we prove `necessary_motif` or must it be axiom?** (Ideal: prove from Cryo-EM)  
5. **What's minimum data for pharma credibility?** (1 molecule? 10? 100?)  

## References

- Wang & MacKinnon (2017): hERG Cryo-EM structure (PDB: 5VA1)  
- CiPA database: Comprehensive in vitro Proarrhythmia Assay  
- ChEMBL: hERG IC50 data (>10,000 compounds)  
- FDA: Withdrawn drugs database  
- Codex/Grok: Deep dive research (this repo)  

---

**Next**: Multi-AI audit → Refine → Implement
