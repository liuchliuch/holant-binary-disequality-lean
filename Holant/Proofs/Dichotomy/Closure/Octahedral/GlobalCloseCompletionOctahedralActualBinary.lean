import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralDressing

/-! Any algebraic matrix on a proved marked O line has an actual original
representative with its own algebraic scalar. The scalar is read from a unit
entry; it is never assumed to descend from an analytic coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralActualBinary
open Holant Holant.Tractable Holant.Algebraic Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family) (f : Form)
variable (literal : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f)

include literal in
theorem actual_scaled (B : Matrix Bool Bool AlgebraicComplex)
    (pivot : B false false=1)
    (member : Direction f (B.map (algebraicClosure ℚ ℂ).val.toRingHom)) :
    ∃ c : AlgebraicComplex,c≠0 ∧ Gadget.Realizes (ClosureSourceRows.ambientFamily G P)
      .disequality (kernelSignature (c • B)) := by
  let Z := B.map (algebraicClosure ℚ ℂ).val.toRingHom
  have hm : Direction f (nativePair Z) :=
    direction_mul (direction_mul (direction_X f) member) (direction_X f)
  obtain ⟨j,d,hd,he⟩ := GlobalCloseCompletionOctahedralCards.kernel_alignment
    (ClosureSourceRows.embedding G) P.family tau f literal (nativePair Z) hm
  have hZ : nativePair (nativePair Z)=Z := by
    ext u v
    simp only [nativePair_apply,Bool.not_not]
  rw [hZ] at he
  let A := ClosureSourceRows.representative G P tau j
  let c : AlgebraicComplex := A false false
  have hc : (c : ℂ)=d := by
    have h := congrFun (congrFun he false) false
    change (c : ℂ)=d*(B false false : ℂ) at h
    simpa only [pivot,OneMemClass.coe_one,mul_one] using h
  have hn : c≠0 := by
    intro hz
    apply hd
    simpa only [hz,ZeroMemClass.coe_zero] using hc.symm
  have exactValue : A=c • B := by
    funext u v
    apply Subtype.val_injective
    have h := congrFun (congrFun he u) v
    change (A u v : ℂ)=d*(B u v : ℂ) at h
    change (A u v : ℂ)=(c : ℂ)*(B u v : ℂ)
    rwa [hc]
  refine ⟨c,hn,?_⟩
  rw [←exactValue]
  exact ClosureSourceRows.representative_actual G P tau j

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralActualBinary
end
