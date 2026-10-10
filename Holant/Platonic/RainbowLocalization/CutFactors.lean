import Holant.Platonic.RainbowLocalization.PresentationLine

/-! Literal matching factors on the two sides of an invariant port cut. -/
noncomputable section
namespace Holant.Platonic.RainbowLocalization
open Holant Holant.Pauli.ExoticKlein
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
namespace MatchingCut
variable {P : Type*} [Fintype P] [DecidableEq P] {r : ℕ}

def Closed (M : Matching P r) (s : P → Bool) : Prop := ∀ p, s (M.mate p) = s p

theorem closed_cut (M : Matching P r) (S : Finset P)
    (hS : ∀ p ∈ S, M.mate p ∈ S) : Closed M (cut S) := by
  intro p
  by_cases hp : p ∈ S
  · simp [cut,hp,hS p hp]
  · have hm : M.mate p ∉ S := by
      intro hh
      exact hp (by simpa using hS (M.mate p) hh)
    simp [cut,hp,hm]

theorem crossing_isEmpty (M : Matching P r) (s : P → Bool) (hc : Closed M s) :
    IsEmpty (Crossing M s) := by
  refine ⟨fun e => ?_⟩
  have hh := hc (M.ports (e.val,false))
  rw [M.mate_port] at hh
  exact e.property hh.symm

/-- With no crossing edges, the internal endpoints are all original ports
of that side.  The equivalence retains their original endpoint order. -/
def factorPorts (M : Matching P r) (s : P → Bool) (b : Bool) (hc : Closed M s) :
    (Internal M s b × Bool) ≃ Side s b := by
  letI := crossing_isEmpty M s hc
  exact (Equiv.sumEmpty (Internal M s b × Bool) (Crossing M s)).symm.trans (sidePorts M s b)

@[simp] theorem factorPorts_apply (M : Matching P r) (s : P → Bool) (b : Bool)
    (hc : Closed M s) (e : Internal M s b) (t : Bool) :
    factorPorts M s b hc (e,t) = sidePorts M s b (.inl (e,t)) := rfl

/-- The actual side tensor, with its specified global coefficient. -/
def factor (M : Matching P r) (s : P → Bool) (b : Bool)
    (A : Fin r → Matrix Bool Bool ℂ) (c : ℂ) : Tensor ℂ (Side s b) :=
  fun x => c * ∏ e : Internal M s b,
    A e.val (x (sidePorts M s b (.inl (e,false)))) (x (sidePorts M s b (.inl (e,true))))

theorem factor_smul (M : Matching P r) (s : P → Bool) (b : Bool)
    (A : Fin r → Matrix Bool Bool ℂ) (c d : ℂ) :
    factor M s b A (d*c) = d • factor M s b A c := by
  funext x
  simp only [factor,Pi.smul_apply,smul_eq_mul,mul_assoc]

def factorPresentation (D : Presentation ℂ P) (s : P → Bool) (b : Bool)
    (hc : Closed (presentationMatching D) s) (c : ℂ) : Presentation ℂ (Side s b) :=
  Presentation.ofFinite (factorPorts (presentationMatching D) s b hc)
    (fun e : Internal (presentationMatching D) s b => D.matrix e.val) c

theorem factorPresentation_tensor (D : Presentation ℂ P) (s : P → Bool) (b : Bool)
    (hc : Closed (presentationMatching D) s) (c : ℂ) :
    (factorPresentation D s b hc c).tensor = factor (presentationMatching D) s b D.matrix c := by
  rw [factorPresentation,Presentation.ofFinite_tensor]
  rfl

theorem factorPresentation_det (D : Presentation ℂ P) (s : P → Bool) (b : Bool)
    (hc : Closed (presentationMatching D) s) (c : ℂ)
    (hD : ∀ e, (D.matrix e).det ≠ 0) :
    ∀ e, ((factorPresentation D s b hc c).matrix e).det ≠ 0 := by
  intro e
  exact hD _

@[simp] theorem factorPresentation_scalar (D : Presentation ℂ P) (s : P → Bool) (b : Bool)
    (hc : Closed (presentationMatching D) s) (c : ℂ) :
    (factorPresentation D s b hc c).scalar = c := rfl

theorem factor_nonzero (D : Presentation ℂ P) (s : P → Bool) (b : Bool)
    (hc : Closed (presentationMatching D) s) (c : ℂ) (hcn : c ≠ 0)
    (hD : ∀ e, (D.matrix e).det ≠ 0) : factor (presentationMatching D) s b D.matrix c ≠ 0 := by
  rw [← factorPresentation_tensor D s b hc c]
  exact productValue_nonzero _ _ _ (factorPresentation_det D s b hc c hD) hcn

/-- The restricted matching is the original mate involution on the actual
side's ports, not a separately supplied matching. -/
theorem factorPresentation_mate (D : Presentation ℂ P) (s : P → Bool) (b : Bool)
    (hc : Closed (presentationMatching D) s) (c : ℂ) (p : Side s b) :
    ((presentationMatching (factorPresentation D s b hc c)).mate p).val =
      (presentationMatching D).mate p.val := by
  let M := presentationMatching (factorPresentation D s b hc c)
  obtain ⟨⟨e,t⟩,rfl⟩ := M.ports.surjective p
  rw [M.mate_port]
  let e' : Internal (presentationMatching D) s b :=
    (Fintype.equivFin (Internal (presentationMatching D) s b)).symm e
  change (presentationMatching D).ports (e'.val,!t) =
    (presentationMatching D).mate ((presentationMatching D).ports (e'.val,t))
  exact ((presentationMatching D).mate_port e'.val t).symm

/-- Invariant cuts split the original matching product into two actual
matching products, without changing or permuting any surviving port. -/
theorem product_eq_factors (M : Matching P r) (s : P → Bool) (hc : Closed M s)
    (A : Fin r → Matrix Bool Bool ℂ) (c : ℂ) (x : P → Bool) :
    productValue M.ports A c x =
      factor M s true A c (fun p => x p.val) * factor M s false A 1 (fun p => x p.val) := by
  letI := crossing_isEmpty M s hc
  change c * (∏ e, A e (x (M.ports (e,false))) (x (M.ports (e,true)))) =
    (c * ∏ e : Internal M s true, A e.val (x (M.ports (e.val,false))) (x (M.ports (e.val,true)))) *
    (1 * ∏ e : Internal M s false, A e.val (x (M.ports (e.val,false))) (x (M.ports (e.val,true))))
  rw [prod_edgeParts M s]
  simp [mul_assoc]

theorem flatten_eq_outer_factors (D : Presentation ℂ P) (s : P → Bool)
    (hc : Closed (presentationMatching D) s) :
    flatten s D.tensor = Matrix.vecMulVec
      (factor (presentationMatching D) s true D.matrix D.scalar)
      (factor (presentationMatching D) s false D.matrix 1) := by
  ext x y
  have he := product_eq_factors (presentationMatching D) s hc D.matrix D.scalar (joinAssignment s x y)
  simpa only [flatten,Presentation.tensor,Matrix.vecMulVec_apply,
    joinAssignment_true,joinAssignment_false,presentationMatching] using he

end MatchingCut
end Holant.Platonic.RainbowLocalization
