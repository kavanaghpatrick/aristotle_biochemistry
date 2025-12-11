/-
# hERG Potassium Channel Binding Site Formalization

Based on PDB structure 7CN0 (cryo-EM, 3.9 Å resolution)

## Binding Site Composition
- 6 key residues: Phe656, Tyr652, Phe619, Phe623, Phe624, Phe625
- 216 atoms total (54 per chain × 4 chains)
- Cavity center: (159.12, 159.12, 127.62) Å
- Cavity volume: 7797.84 Å³ (conservative sphere estimate)

## Critical Residue
- Phe656 (CA atoms): ~12.35 Å from cavity center (all 4 chains)
- Known pi-stacking interaction site for hERG blockers

## Conservative Assumptions
- Volume: Upper bound from sphere fit (may overestimate true cavity)
- For safety proofs, overestimation is acceptable (fewer false positives)
-/

import BiochemFormal.Geometry.Core
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace BiochemFormal.Geometry.HERG

open BiochemFormal.Geometry

/-! ## hERG Cavity Constants -/

/--
Center of hERG binding cavity (PDB 7CN0).

Coordinates in Ångströms from PDB origin.
Calculated as centroid of key aromatic residues (Phe656, Tyr652, Phe619, Phe623-625).
-/
def herg_cavity_center : Point3D :=
  (159.11975019949455, 159.12025006612143, 127.62250024301035)

/--
hERG binding cavity volume (Ångströms³).

Conservative estimate from bounding sphere of aromatic residues.
Using 7797.84 Å³ from sphere fit (larger than convex hull 3929 Å³).

For formal safety proofs, overestimating cavity volume is conservative:
- Larger cavity → harder to prove exclusion
- Reduces false positives (safer)
-/
def herg_cavity_volume : ℝ := 7797.84

/--
Phe656 alpha-carbon distance from cavity center (Ångströms).

Critical residue for pi-stacking interactions with hERG blockers.
Average of 4 chains: ~12.35 Å
-/
def phe656_distance : ℝ := 12.35

/--
Maximum distance for pi-stacking interactions (Ångströms).

Conservative estimate for aromatic pi-pi interactions.
Literature range: 3.5-6.0 Å (using upper bound for safety).
-/
def pi_stacking_max_distance : ℝ := 6.0

/-! ## Binding Site Structure -/

/--
Represents the hERG binding site with formal geometric properties.
-/
structure HERGBindingSite where
  cavity_center : Point3D
  cavity_volume : ℝ
  cavity_volume_pos : cavity_volume > 0
  phe656_dist : ℝ
  phe656_dist_pos : phe656_dist > 0

/--
The concrete hERG binding site from PDB 7CN0.
-/
def herg_site : HERGBindingSite :=
  { cavity_center := herg_cavity_center
    cavity_volume := herg_cavity_volume
    cavity_volume_pos := by norm_num [herg_cavity_volume]
    phe656_dist := phe656_distance
    phe656_dist_pos := by norm_num [phe656_distance] }

/-! ## Basic Properties -/

/--
The hERG cavity volume is positive.
-/
theorem herg_cavity_volume_pos : herg_cavity_volume > 0 := by
  norm_num [herg_cavity_volume]

/--
Phe656 distance is positive.
-/
theorem phe656_distance_pos : phe656_distance > 0 := by
  norm_num [phe656_distance]

/--
Pi-stacking maximum distance is positive.
-/
theorem pi_stacking_distance_pos : pi_stacking_max_distance > 0 := by
  norm_num [pi_stacking_max_distance]

/-! ## Reachability Criterion -/

/--
Minimum radius needed to reach Phe656 from cavity center for pi-stacking.

For a molecule to engage in pi-stacking with Phe656:
- Its atoms must get within 6 Å of Phe656
- Phe656 is at 12.35 Å from center
- Therefore, molecule must reach at least 12.35 - 6.0 = 6.35 Å from center
-/
def min_radius_to_reach_phe656 : ℝ :=
  phe656_distance - pi_stacking_max_distance

/--
The minimum radius to reach Phe656 is positive.
-/
theorem min_radius_to_reach_phe656_pos : min_radius_to_reach_phe656 > 0 := by
  unfold min_radius_to_reach_phe656 phe656_distance pi_stacking_max_distance
  norm_num

/-! ## Verification -/

-- Verify NO custom axioms in hERG definitions
#print axioms herg_site
#print axioms herg_cavity_volume_pos

end BiochemFormal.Geometry.HERG
