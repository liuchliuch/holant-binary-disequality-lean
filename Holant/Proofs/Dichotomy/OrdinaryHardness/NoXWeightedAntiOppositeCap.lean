import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSimplexPhase
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalPair

/-! Preserve both actual ports of each opposite bundle and cap them with the
actual weighted antidiagonal. Exposed incidence becomes even without a literal
X gate, and restriction to the simplex code has its exact weighted phase. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiOppositeCap
open Holant Holant.Tractable
open scoped BigOperators
open OrdinaryNegativeMixedBlockData
namespace U
export OrdinaryNegativeXUniversalResource (Kind OddResource EvenBad)
end U
namespace P
export OrdinaryNegativeXUniversalPair (arity table block block_ambient evenBad_of_coefficient)
end P
namespace L
export OrdinaryNegativeMixedBlockLiteral (nodes nodes_ports nodes_value)
end L
namespace A
export NoXWeightedAntiSigned (anti)
end A
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable (kind : U.Kind)
abbrev size := kind.arity

def opposite (z : Fin (size kind)→Bool) : Fin (size kind+size kind)→Bool :=
  Fin.addCases z (fun i=>!(z i))

def embedding (x : Fin kind.rank→Bool) : Fin (size kind+size kind)→Bool :=
  opposite kind (kind.code x)

theorem opposite_affine : TwoTranslate.IsAffineMap (opposite kind) := by
  intro x y
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [opposite,AffinePhase.xor,AffinePhase.origin,Fin.addCases_left]
    cases x j <;> cases y j <;> rfl
  · intro j
    simp only [opposite,AffinePhase.xor,AffinePhase.origin,Fin.addCases_right]
    cases x j <;> cases y j <;> rfl

theorem embedding_affine : TwoTranslate.IsAffineMap (embedding kind) := by
  change TwoTranslate.IsAffineMap (fun x=>opposite kind (kind.code x))
  exact Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget.affine_comp
    (opposite kind) kind.code (opposite_affine kind) (OrdinaryNegativeXUniversalResource.Kind.code_affine kind)

def cap : Recipe (u:=1) (s:=2) (a:=fun _=>size kind+size kind)
    (b:=P.arity (size kind+size kind) 2) := fun _=>
  ⟨0,fun j=>.inr j⟩::List.ofFn (fun q : Fin (size kind)=>
    ⟨1,![.inr (Fin.castAdd (size kind) q),.inr (Fin.natAdd (size kind) q)]⟩)

theorem cap_even : EvenRecipe (cap kind) := by
  intro i q
  fin_cases i
  cases kind <;> cases q with
  | inl bit => cases bit <;> decide
  | inr j => fin_cases j <;> decide

variable {K : Type} [Field K]
variable (f : Signature K (size kind+size kind)) (v w : K)

theorem coefficient_exact (z : Fin (size kind+size kind)→Bool) :
    coefficient (P.table f (A.anti v w)) (cap kind) 0 z=
      f z*∏q : Fin (size kind),A.anti v w ![z (Fin.castAdd (size kind) q),z (Fin.natAdd (size kind) q)] := by
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    cap,List.map_cons,List.prod_cons,List.map_ofFn,List.prod_ofFn]
  rfl

theorem coefficient_embedding (x : Fin kind.rank→Bool) :
    coefficient (P.table f (A.anti v w)) (cap kind) 0 (embedding kind x)=
      (∏i,if kind.code x i then w else v)*f (embedding kind x) := by
  rw [coefficient_exact,mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [embedding,opposite,Fin.addCases_left,Fin.addCases_right]
  cases kind.code x i <;> simp [A.anti]

section Actual
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (antiLabel : Fin s)
variable (v w : K)
variable (ha_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,A.anti v w⟩)

def antiResource : U.OddResource (s:=s) b 2 where
  privateCount := 0
  rows := fun i=>L.nodes i antiLabel (congrArg Sigma.fst ha_lit) [fun j=>.inr j]
  constant_even q := by
    change Even (((L.nodes (a:=fun _=>2+0) (0 : Fin 1) antiLabel _ [fun j=>.inr j]).flatMap
      (fun node=>List.ofFn node.2)).count (.inl q))
    rw [L.nodes_ports]
    cases q <;> decide
  boundary_odd i := by
    change Odd (((L.nodes (a:=fun _=>2+0) (0 : Fin 1) antiLabel _ [fun j=>.inr j]).flatMap
      (fun node=>List.ofFn node.2)).count (.inr (Fin.castAdd 0 i)))
    rw [L.nodes_ports]
    fin_cases i <;> decide
  private_even i := Fin.elim0 i

theorem anti_ambient : (antiResource H antiLabel v w ha_lit).ambient H=
    A.anti (v : AlgebraicComplex) (w : AlgebraicComplex) := by
  funext z
  change ((∑y : Fin 0→Bool,coefficient H
    (fun i=>L.nodes (a:=fun _=>2+0) i antiLabel (congrArg Sigma.fst ha_lit) [fun j=>.inr j])
    0 (Fin.addCases z y) : K) : AlgebraicComplex)=_
  simp only [Fintype.sum_unique]
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient
  erw [L.nodes_value H 0 antiLabel (A.anti v w) ha_lit]
  cases hz0 : z 0 <;> cases hz1 : z 1 <;>
    simp [Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle.evaluate,
      T.substitute,A.anti,Fin.addCases,hz0,hz1]

variable (resource : U.OddResource (s:=s) b (size kind+size kind))

include ha_lit in
/-- The premise is an exact small weighted-phase obstruction, independent
of any source/compiler. Every row emitted here is an actual original label. -/
theorem evenBad_of_compressed
    (bad : ¬Affine (fun x : Fin kind.rank→Bool=>
      (∏i,if kind.code x i then (w : AlgebraicComplex) else (v : AlgebraicComplex))*
        resource.ambient H (embedding kind x))) : U.EvenBad H := by
  apply P.evenBad_of_coefficient resource (antiResource H antiLabel v w ha_lit) H (cap kind) (cap_even kind)
  intro h
  have hh := h.precompose (embedding kind) (embedding_affine kind)
  apply bad
  rw [anti_ambient] at hh
  simpa only [coefficient_embedding] using hh

include ha_lit in
/-- The genuine opposite-bundle Affine resource is consumed directly by an
actual weighted-antidiagonal row with opposite fourth powers. -/
theorem evenBad_of_affine_compressed (hv : v≠0) (hw : w≠0)
    (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))
    (affine : Affine (fun x : Fin kind.rank→Bool=>resource.ambient H (embedding kind x)))
    (full : ∀x : Fin kind.rank→Bool,resource.ambient H (embedding kind x)≠0) : U.EvenBad H := by
  apply evenBad_of_compressed kind H antiLabel v w ha_lit resource
  exact NoXWeightedAntiSimplexPhase.code_not_affine kind (v : AlgebraicComplex) (w : AlgebraicComplex)
    (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) fourth _ affine full
end Actual


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiOppositeCap
end
