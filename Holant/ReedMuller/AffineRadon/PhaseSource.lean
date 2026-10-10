import Holant.ReedMuller.AffineRadon.NormalForm
import Holant.ReedMuller.AffineRadon.PhaseSupport
import Holant.ReedMuller.AffineRadon.PhaseConstants

/-! Source-affine APIs for the coefficient and cancellation arguments of
Lemma 7.19, with faithful algebraic-complex to complex transport. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {f : Signature AlgebraicComplex n}

@[simp] theorem ActualNormalForm.phaseValue_eq (A : ActualNormalForm f) (x : BinaryVector n) :
    phaseValue A.scalar A.shift A.direction A.phase x=f (wordVector x) :=
  (A.exact_value x).symm

/-- No derivative or cancellation assumption: the source normal form itself
supplies the phase ratio and the exact signed support equation. -/
theorem ActualNormalForm.signed_support (A : ActualNormalForm f)
    (s : BinaryVector n) (hs : s∈A.direction) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2, ∀ b x,
      (f (wordVector x)+phaseSign b*f (wordVector (x+s))≠0) ↔
        x-A.shift∈A.direction ∧
          (α=1 ∨ α=3 ∨ (α=0 ∧ ell x=b) ∨ (α=2 ∧ ell x=b+1)) := by
  simpa only [A.phaseValue_eq] using
    phaseValue_signed_support A.scalar A.scalar_ne_zero A.shift A.direction A.phase s hs

/-- The complete locus alternative for the actual affine signature. -/
theorem ActualNormalForm.signed_locus (A : ActualNormalForm f)
    (s : BinaryVector n) (hs : s∈A.direction) (b : ZMod 2) :
    (∀ x, f (wordVector x)+phaseSign b*f (wordVector (x+s))=0) ∨
    (∀ x, (f (wordVector x)+phaseSign b*f (wordVector (x+s))≠0) ↔ x-A.shift∈A.direction) ∨
    (∃ (y : BinaryVector n) (D : BinaryCode n), y-A.shift∈A.direction ∧ D≤A.direction ∧ s∈D ∧
      Module.finrank (ZMod 2) D+1=Module.finrank (ZMod 2) A.direction ∧
      ∀ x, (f (wordVector x)+phaseSign b*f (wordVector (x+s))≠0) ↔ x-y∈D) := by
  simpa only [A.phaseValue_eq] using
    phaseValue_signed_locus A.scalar A.scalar_ne_zero A.shift A.direction A.phase s hs b

/-- The ratio has the source's exact fourth root and affine binary sign. -/
theorem ActualNormalForm.phase_ratio (A : ActualNormalForm f)
    (s : BinaryVector n) (hs : s∈A.direction) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2, ∀ x,
      x-A.shift∈A.direction →
        f (wordVector (x+s))/f (wordVector x)=fourthRootPhase α*phaseSign (ell x) := by
  obtain ⟨α,ell,_,hr⟩ := phaseValue_translation A.scalar A.scalar_ne_zero
    A.shift A.direction A.phase s hs
  exact ⟨α,ell,by simpa only [A.phaseValue_eq] using hr⟩

/-- Faithful transport of the actual numerator, including its exterior sign,
to the ordinary complex coefficient field used by Radon cards. -/
@[simp] theorem coe_signed_numerator (b : ZMod 2) (z w : AlgebraicComplex) :
    ((z+phaseSign b*w : AlgebraicComplex) : ℂ)=
      (z : ℂ)+CharacterFlat.sign b*(w : ℂ) := by
  simp

/-- The support classification is unchanged in the source Radon coefficient
field; in particular no zero or scalar information is lost by embedding. -/
theorem ActualNormalForm.complex_signed_locus (A : ActualNormalForm f)
    (s : BinaryVector n) (hs : s∈A.direction) (b : ZMod 2) :
    (∀ x, (f (wordVector x) : ℂ)+CharacterFlat.sign b*(f (wordVector (x+s)) : ℂ)=0) ∨
    (∀ x, ((f (wordVector x) : ℂ)+CharacterFlat.sign b*(f (wordVector (x+s)) : ℂ)≠0) ↔
      x-A.shift∈A.direction) ∨
    (∃ (y : BinaryVector n) (D : BinaryCode n), y-A.shift∈A.direction ∧ D≤A.direction ∧ s∈D ∧
      Module.finrank (ZMod 2) D+1=Module.finrank (ZMod 2) A.direction ∧
      ∀ x, ((f (wordVector x) : ℂ)+CharacterFlat.sign b*(f (wordVector (x+s)) : ℂ)≠0) ↔ x-y∈D) := by
  have he (x : BinaryVector n) :
      ((f (wordVector x) : ℂ)+CharacterFlat.sign b*(f (wordVector (x+s)) : ℂ)=0) ↔
        f (wordVector x)+phaseSign b*f (wordVector (x+s))=0 := by
    rw [←coe_signed_numerator]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg (fun z : AlgebraicComplex => (z : ℂ)) h
  simpa only [he,ne_eq] using A.signed_locus s hs b

/-- The final coefficient step of Lemma 7.19, after the geometric argument
has supplied a self-dual support and three actual constant orbit sums. -/
theorem ActualNormalForm.flat_of_three_orbit_sums (A : ActualNormalForm f)
    (hU : SelfDual A.direction) (p q : BinaryVector n) (hpU : p∈A.direction)
    (cp cq cpq : ℂ)
    (hp : ∀ x, x-A.shift∈A.direction →
      (f (wordVector x) : ℂ)+(f (wordVector (x+p)) : ℂ)=cp)
    (hq : ∀ x, x-A.shift∈A.direction →
      (f (wordVector x) : ℂ)+(f (wordVector (x+q)) : ℂ)=cq)
    (hpq : ∀ x, x-A.shift∈A.direction →
      (f (wordVector x) : ℂ)+(f (wordVector (x+(p+q))) : ℂ)=cpq) :
    Flat (fun x => (f x : ℂ)) := by
  classical
  let g : BinaryVector n → ℂ := fun x => (f (wordVector x) : ℂ)
  let k : ℂ := (cpq-cq+cp)/2
  have hg : ∀ x, x-A.shift∈A.direction → g x=k :=
    constant_on_support_of_three_orbit_sums g A.shift A.direction p q hpU cp cq cpq hp hq hpq
  have ha : A.shift-A.shift∈A.direction := by simp
  have hga : g A.shift≠0 := by
    have hfa := (A.support f A.shift).mpr ha
    change (f (wordVector A.shift) : ℂ)≠0
    exact_mod_cast hfa
  have hk : k≠0 := by
    rw [←hg A.shift ha]
    exact hga
  refine ⟨Units.mk0 k hk,A.shift,A.direction,hU,?_⟩
  funext x
  change (f x : ℂ)=if vectorWord x-A.shift∈A.direction then k else 0
  split_ifs with hx
  · simpa only [g,word_vector] using hg (vectorWord x) hx
  · have hz : f x=0 := by
      by_contra hn
      exact hx ((A.support f (vectorWord x)).mp (by simpa only [word_vector] using hn))
    simp only [hz,ZeroMemClass.coe_zero]

end
end Holant.ReedMuller.AffineRadon
