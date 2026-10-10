import Holant.Certificates.AffineEndpoint.PhaseCodes

/-! Intrinsic phase classification on genuine affine support charts. The chart
is a bijection onto the actual support, and both maps are affine Boolean maps. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def chartSignature {d n : ℕ} (S : AffineSystem n) (coordinates : Word n → Word d)
    (p : PhaseParameters d) : Signature AlgebraicComplex n :=
  fun x => if S.Holds x then phaseValue p (coordinates x) else 0

 theorem chartSignature_affine {d n : ℕ} (S : AffineSystem n) (coordinates : Word n → Word d)
    (hc : IsAffineMap coordinates) (p : PhaseParameters d) :
    Affine (chartSignature S coordinates p) :=
  ((phaseValue_affine p).precompose coordinates hc).restrict S

 theorem phaseValue_ne_zero {d : ℕ} (p : PhaseParameters d) (y : Word d) : phaseValue p y≠0 :=
  fourthRootPhase_ne_zero _

 theorem chartSignature_ne_zero_iff {d n : ℕ} (S : AffineSystem n) (coordinates : Word n → Word d)
    (p : PhaseParameters d) (x : Word n) : chartSignature S coordinates p x≠0 ↔ S.Holds x := by
  by_cases h : S.Holds x <;> simp [chartSignature,h,phaseValue_ne_zero]

 theorem chart_phase_coverage {d n : ℕ} (S : AffineSystem n)
    (chart : Word d → Word n) (coordinates : Word n → Word d)
    (hc : IsAffineMap chart)
    (hchart : ∀y,S.Holds (chart y))
    (hinverse : ∀x,S.Holds x→chart (coordinates x)=x)
    (f : Signature AlgebraicComplex n) (hf : Affine f)
    (hs : ∀x,f x≠0 ↔ S.Holds x) (h0 : f (chart (origin d))=1) :
    ∃c : Fin (phaseCodeCount d),f=chartSignature S coordinates (phaseDecode d c) := by
  obtain ⟨p,hp⟩ := normalized_full_phase_coverage (fun y => f (chart y))
    (hf.precompose chart hc) (fun y => (hs _).mpr (hchart y)) h0
  obtain ⟨c,rfl⟩ := phaseDecode_surjective d p
  refine ⟨c,?_⟩
  funext x
  by_cases hx : S.Holds x
  · simpa [chartSignature,hx,hinverse x hx] using congrFun hp (coordinates x)
  · have hz : f x=0 := Classical.not_not.mp (fun hn => hx ((hs x).mp hn))
    simp [chartSignature,hx,hz]

end
end Holant.Certificates.AffineEndpoint
