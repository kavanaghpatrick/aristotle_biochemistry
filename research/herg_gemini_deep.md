(node:86791) [DEP0040] DeprecationWarning: The `punycode` module is deprecated. Please use a userland alternative instead.
(Use `node --trace-deprecation ...` to show where the warning was created)
(node:86806) [DEP0040] DeprecationWarning: The `punycode` module is deprecated. Please use a userland alternative instead.
(Use `node --trace-deprecation ...` to show where the warning was created)
Loaded cached credentials.
Here is the research proposal and implementation plan for the formal verification of hERG toxicity.

### 1. Scientific Summary: The "Greasy Trap" Problem
hERG binding is notoriously difficult to predict because the channel’s inner cavity is unusually large, hydrophobic, and promiscuous. Unlike "lock-and-key" receptors, hERG functions as a "greasy trap."
*   **Mechanism:** Most blockers enter the intracellular gate when the channel opens and get trapped in the central cavity. They stabilize the closed state or physically occlude the pore.
*   **Key Features:** The cavity is lined with aromatic residues (Tyr652, Phe656) that engage in pi-stacking interactions with drug molecules.
*   **The Difficulty:** The binding is driven by non-specific hydrophobic interactions and the cavity can accommodate a vast diversity of shapes. Predicting *affinity* ($K_d$) requires complex thermodynamic integration (impossible to formalize simply).
*   **The Opportunity:** While affinity is hard, **exclusion** is binary. To block the pore, the drug must physically *enter* it. If we can prove the drug is sterically incapable of entering the open gate (geometric exclusion) or essentially incapable of crossing the membrane to access the fenestrations (physicochemical exclusion), we can formally certify safety.

### 2. Formal Approach: Geometric Reachability Analysis
To maximize simplicity and rigor, we should strictly avoid thermodynamic predictions. Instead, we model this as a **Geometric Reachability Problem**.

**The Logic:**
1.  **Premise 1 (The Trap):** To cause toxicity, the molecule $M$ must enter region $R$ (the hERG cavity).
2.  **Premise 2 (Access):** Access to $R$ is guarded by a set of geometric bottlenecks $B$ (the intracellular gate and hydrophobic fenestrations).
3.  **Proof Strategy:** We prove that the *minimum rigid volume* of $M$ is strictly larger than the *maximum flexible aperture* of any bottleneck in $B$.

**Why Simplest:**
*   **Discrete vs. Continuous:** We don't need continuous molecular dynamics. We only need the "lower bound" shape of the drug and "upper bound" shape of the pore.
*   **Convex Hulls:** We can approximate the drug as a union of hard spheres and the pore as a mesh. If the intersection of the drug's hull and the pore's "forbidden zone" is empty for all rigid transformations, binding is impossible.
*   **Conservative Safety:** This produces false positives (says a drug is unsafe if it fits but doesn't bind) but **zero false negatives** (never says a drug is safe if it can enter). This is the gold standard for verification.

### 3. Lean 4 Formalization Sketch
We rely on `Mathlib.Analysis.Convex` and `Mathlib.MetricSpace`.

```lean
import Mathlib.Analysis.Convex.Basic
import Mathlib.Geometry.Euclidean.Basic

namespace hERG_Verification

-- 1. Define the Molecule as a rigid set of atoms (hard spheres)
structure Atom where
  pos : EuclideanSpace ℝ (Fin 3)
  vdw_radius : ℝ

def Molecule := List Atom

-- 2. Define the Pore BottleNeck (simplified as a Cylinder for MVP)
-- In reality, this would be a mesh derived from PDB 5VA1
structure Cylinder where
  center : EuclideanSpace ℝ (Fin 3)
  radius : ℝ
  height : ℝ

-- 3. Define the concept of "Fitting"
-- A molecule fits if there exists a rigid transformation (rotation + translation)
-- such that all atoms are contained within the cylinder.
def fits_inside (m : Molecule) (c : Cylinder) : Prop :=
  ∃ (rot : LinearIsometryEquiv (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    (trans : EuclideanSpace ℝ (Fin 3)),
    ∀ a ∈ m,
      let new_pos := rot a.pos + trans
      -- Check if point is inside cylinder geometry
      (new_pos.x^2 + new_pos.y^2 < c.radius^2) ∧ 
      (new_pos.z ≥ 0 ∧ new_pos.z ≤ c.height)

-- 4. The Safety Theorem
-- If the molecule's minimum bounding sphere is larger than the pore,
-- it is provably impossible for it to fit.
def min_bounding_sphere_radius (m : Molecule) : ℝ := sorry -- implementation needed

theorem safety_by_exclusion (m : Molecule) (c : Cylinder) :
  (min_bounding_sphere_radius m > c.radius) → ¬ fits_inside m c := by
  sorry -- Proof uses geometric inequality properties

end hERG_Verification
```

### 4. Feasibility Assessment
*   **Aristotle Capability:** **High.** The reasoning is strictly logical and geometric ("If A > B, then A won't fit in B"). Aristotle does not need to "understand" chemistry, only 3D geometry constraints.
*   **Data Availability:** The hERG structure (PDB: 5VA1) gives us the coordinates. Calculating the "Maximum Pore Radius" is a solved problem (using tools like HOLE or MOLE, which we can import as constants).
*   **Risk:** The main risk is protein flexibility (breathing). We must define a "Safety Margin" (e.g., Pore Radius + 2Å) to account for structural fluctuations.

### 5. MVP Definition: The "Bulky-Safe" Proof
**Goal:** Prove that **Vancomycin** (or a similarly massive, rigid drug) cannot cause hERG toxicity via pore blocking.
*   **Input:** Vancomycin structure (SMILES/PDB).
*   **Constraint:** hERG Intracellular Gate diameter ($\approx 12$ Å).
*   **Proof:** Calculate Vancomycin's minimal cross-sectional width ($> 15$ Å).
*   **Output:** A Lean proof checking `width_drug > width_pore` leads to `False` for the proposition `IsToxic`.
*   **Value:** Demonstrates end-to-end pipeline: Structure $\to$ Lean Definition $\to$ Formal Verification.

### 6. Implementation Plan

| Step | Action | Tool/Method | Output |
| :--- | :--- | :--- | :--- |
| **1** | **Define Geometry** | `Mathlib` | Create `RigidBody.lean` with simple exclusion theorems (Sphere vs Cylinder). |
| **2** | **Get Pore Specs** | `Web Search` / `PDB` | Determine the authoritative "Max Open Diameter" of hERG (likely $\approx 11-13$Å). |
| **3** | **Molecule Parser** | `Python` Script | Write a script to convert `.sdf` or `.pdb` files into Lean `List Atom` definitions. |
| **4** | **Width Calculator** | `Lean` Function | Implement a function in Lean that calculates the bounding box/width of the molecule. |
| **5** | **Verify MVP** | `Lean` Proof | Run the proof on a "Safe Giant" molecule and a "Known Toxic" (small) molecule (proof should fail for toxic). |

### Immediate Next Step
I recommend we start by creating the **Lean geometry definitions** (Step 1) and a **Python script** (Step 3) to generate the Lean code for a sample molecule. This bridges the gap between chemical data and formal verification.
