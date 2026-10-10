import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinEq4Source
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinFiniteEq4
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinBAlgebra
import Holant.Proofs.Dichotomy.Main.PaperControlled.KleinDenseSeparated
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseResolved

/-! A separating B-coordinate image of an actual standard-Klein table is
consumed by the existing genuine B native source. The Pauli multiplier is
transported projectively, and the positive common basis is pulled back on the
whole original current family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinBResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion
namespace F
export PaperControlled.KleinFiniteEq4 (Input classified)
end F
namespace C
export GlobalCloseCompletionBCoordinateRealizes (family identity forward)
end C
namespace R
export GlobalCloseCompletionBDenseRepresentatives (family_finite_eq)
end R
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem action_scale {n : ℕ} (U : InvertibleKernel) (c : AlgebraicComplex)
    (f : Signature AlgebraicComplex n) : U.action (fun x=>c*f x)=fun x=>c*U.action f x := by
  funext x
  simp only [InvertibleKernel.action,Signature.coordinateAction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem forward_upTo (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    {n : ℕ} (f : Signature AlgebraicComplex n) (actual : Gadget.RealizesUpTo F .disequality f) :
    Gadget.RealizesUpTo (C.family F) .disequality (basisB.symm.action f) := by
  obtain ⟨c,hc,actual⟩ := actual
  have h := C.forward F hI _ actual
  rw [action_scale] at h
  obtain ⟨d,hd,h⟩ := h
  refine ⟨d*c,mul_ne_zero hd hc,?_⟩
  convert h using 1
  funext x
  ring

theorem forward_Z (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (actual : Gadget.RealizesUpTo F .disequality (fun x : Fin 2→Bool=>T.Z (x 0) (x 1))) :
    Gadget.RealizesUpTo (C.family F) .disequality (fun x : Fin 2→Bool=>T.Z (x 0) (x 1)) := by
  have h := forward_upTo F hI _ actual
  rw [GlobalCloseCompletionKleinBAlgebra.B_Z] at h
  obtain ⟨d,hd,h⟩ := h
  refine ⟨d*(1/2),mul_ne_zero hd (by norm_num),?_⟩
  convert h using 1
  funext x
  ring

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def input : F.Input G where
  count := P.count+1
  arity := GlobalCloseCompletionBNativeSource.arity G P
  table := GlobalCloseCompletionBNativeCodec.mapped G P
  identity := by rw [←R.family_finite_eq]; exact C.identity _
  source := GlobalCloseCompletionBNativeCodec.source G P

include P in
theorem eq4_classified (actual : Gadget.RealizesUpTo (C.family (ClosureSourceRows.ambientFamily G P))
    .disequality (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex))) :
    PaperControlled.KleinEq4Source.CurrentTract G P ∨ PaperControlled.KleinEq4Source.Hard G := by
  have af : Gadget.RealizesUpTo (PaperControlled.KleinFiniteEq4.family G (input G P))
      .disequality (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex)) := by
    change Gadget.RealizesUpTo (UniversalPairReduction.FiniteFamily.family
      (GlobalCloseCompletionBNativeCodec.mapped G P)) _ _
    rw [←R.family_finite_eq]
    exact actual
  rcases F.classified G (input G P) (GlobalCloseCompletionBDenseResolved.preprocessed G P) af with
      (affine|product|localAffine)|hard
  · exact Or.inl (ClosureNativePresentation.tractX_forward_affine
      (GlobalCloseCompletionBDenseResolved.common G P .affine affine))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_product
      (GlobalCloseCompletionBDenseResolved.common G P .product product))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine
      (GlobalCloseCompletionBDenseResolved.common G P .localAffine localAffine))
  · exact Or.inr hard

variable (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.standard)

include torsion cardinal noncyclic standard in
theorem classified (q : Signature AlgebraicComplex 4)
    (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality q)
    (a b c d : AlgebraicComplex) (form : basisB.symm.action q=T.normal a b c d)
    (separated : (a^2-b^2)^2≠(c^2-d^2)^2) :
    PaperControlled.KleinEq4Source.CurrentTract G P ∨ PaperControlled.KleinEq4Source.Hard G := by
  have z := forward_Z _ (StableDenseGaugeCurrent.ambient_identity G P)
    (PaperControlled.KleinDenseSeparated.pauli_Z G P torsion cardinal noncyclic standard)
  have hq := forward_upTo _ (StableDenseGaugeCurrent.ambient_identity G P) q actual
  rw [form] at hq
  exact eq4_classified G P (GlobalCloseCompletionKleinTwistedActual.normal_eq4 _ (C.identity _) z a b c d hq separated)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.KleinBResolved
end
