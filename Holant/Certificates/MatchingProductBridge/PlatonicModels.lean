import Holant.Certificates.MatchingProductBridge.BridgeIdentities
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Real.Sqrt

/-! The literal T/O/I representative families and matching cones from the current
source. Membership is given by exact quaternion coordinates and nonzero scaling;
no abstract group-closure or cone-classification assumption is introduced. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section

inductive PlatonicModel where
  | tetrahedral | octahedral | icosahedral
  deriving DecidableEq

def quaternionBasis : Fin 4 → Binary := ![Q0,Q1,Q2,Q3]
def quaternion (v : Fin 4 → ℝ) : Binary := fun a b =>
  (v 0 : ℂ)*Q0 a b+(v 1 : ℂ)*Q1 a b+(v 2 : ℂ)*Q2 a b+(v 3 : ℂ)*Q3 a b

def signBit (b : Bool) : ℝ := if b then -1 else 1

def tetrahedralBase (U : Binary) : Prop :=
  (∃ i : Fin 4, U = quaternionBasis i) ∨
    ∃ ε : Fin 3 → Bool, U = quaternion ![1,signBit (ε 0),signBit (ε 1),signBit (ε 2)]

def octahedralBase (U : Binary) : Prop := tetrahedralBase U ∨
  ∃ i j : Fin 4, i < j ∧ ∃ ε : Bool,
    U = quaternionBasis i + (signBit ε : ℂ) • quaternionBasis j

def goldenRatio : ℝ := (1+Real.sqrt 5)/2
def goldenReciprocal : ℝ := goldenRatio⁻¹

def goldenVector (ε : Fin 3 → Bool) : Fin 4 → ℝ :=
  ![0,signBit (ε 0),signBit (ε 1)*goldenRatio,signBit (ε 2)*goldenReciprocal]

def icosahedralBase (U : Binary) : Prop := tetrahedralBase U ∨
  ∃ π : Equiv.Perm (Fin 4), Equiv.Perm.sign π = 1 ∧ ∃ ε : Fin 3 → Bool,
    U = quaternion (fun i => goldenVector ε (π.symm i))

def modelBase : PlatonicModel → Binary → Prop
  | .tetrahedral => tetrahedralBase
  | .octahedral => octahedralBase
  | .icosahedral => icosahedralBase

/-- Saturated actual representatives of the source's projective matrix classes. -/
def groupDirection (g : PlatonicModel) (U : Binary) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ V : Binary, modelBase g V ∧ U = c • V

def matchingProduct (r : Fin 3) (U V : Binary) : FourTensor := ![P0 U V,P1 U V,P2 U V] r

def X : Binary := Holant.Signature.disequality

/-- The source deck uses [UX],[VX] in G; arbitrary nonzero cone scales are retained. -/
def matchingCone (g : PlatonicModel) (f : FourTensor) : Prop := f = 0 ∨
  ∃ r : Fin 3, ∃ U V : Binary, groupDirection g (multiply U X) ∧
    groupDirection g (multiply V X) ∧ ∃ c : ℂ, c ≠ 0 ∧ f = c • matchingProduct r U V

def bridgeConditions (g : PlatonicModel) (W : FourTensor) : Prop :=
  matchingCone g W ∧ matchingCone g (A-(2 : ℂ) • W) ∧ matchingCone g ((2 : ℂ) • W-B)

theorem quaternion_axis_base (g : PlatonicModel) (i : Fin 4) : modelBase g (quaternionBasis i) := by
  cases g
  · exact Or.inl ⟨i,rfl⟩
  · exact Or.inl (Or.inl ⟨i,rfl⟩)
  · exact Or.inl (Or.inl ⟨i,rfl⟩)

theorem quaternion_axis_direction (g : PlatonicModel) (i : Fin 4) : groupDirection g (quaternionBasis i) :=
  ⟨1,one_ne_zero,_,quaternion_axis_base g i,by simp⟩

theorem groupDirection_smul (g : PlatonicModel) {U : Binary} (h : groupDirection g U)
    {c : ℂ} (hc : c ≠ 0) : groupDirection g (c • U) := by
  rcases h with ⟨d,hd,V,hV,rfl⟩
  exact ⟨c*d,mul_ne_zero hc hd,V,hV,by simp [smul_smul]⟩

theorem matchingCone_zero (g : PlatonicModel) : matchingCone g 0 := Or.inl rfl

theorem matchingCone_smul (g : PlatonicModel) {f : FourTensor} (h : matchingCone g f) (c : ℂ) :
    matchingCone g (c • f) := by
  by_cases hc : c = 0
  · subst c; simpa using matchingCone_zero g
  rcases h with rfl | ⟨r,U,V,hU,hV,d,hd,rfl⟩
  · simpa using matchingCone_zero g
  · exact Or.inr ⟨r,U,V,hU,hV,c*d,mul_ne_zero hc hd,by simp [smul_smul]⟩

end
end Holant.Certificates.MatchingProductBridge
