import Holant.Proofs.Hardness.GeneralEOGeneralPhaseBinaryRemoval

/-! Zero-sided and finite nonresonant native binary graphs are actual
pin suppliers over the original family, even if no original row is binary.
The criterion is a finite coefficient test in the fixed generated number field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseBinaryPins
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace A
export GeneralEOTensorPowerRemovalOriginalField (family newLabel family_new)
end A
namespace R
export GeneralEOTensorPowerRemovalRaw (sourceArity)
end R
namespace P
export GeneralEOGeneralPhaseBinaryRemoval (normalized pull_elimination)
end P
namespace C
export GeneralEOOriginalCapSource (coefficient)
end C
namespace F
export GeneralEONonARSPinningFiniteCap (Coefficients exponent)
end F
namespace Z
export GeneralEOZeroSidedCapSource (Coefficients)
end Z
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (f : Signature AlgebraicComplex 2)

def ports : Fin (R.sourceArity s 2 a s) ≃ (Fin 2 ⊕ (Fin 0×Bool)) :=
  (finCongr (by simp [R.sourceArity])).trans (Equiv.sumEmpty (Fin 2) (Fin 0×Bool)).symm

private theorem cast_apply {m k : ℕ} (h : m=k) (g : Signature AlgebraicComplex m)
    (x : Fin k→Bool) : Holant.LocalDrafts.BinaryInterpolation.OriginalTables.castSignature h g x=
      g (fun i => x (Fin.cast h i)) := by
  subst k
  rfl

theorem coefficient (x : Fin 2→Bool) :
    C.coefficient (A.family G f) A.newLabel (ports (s:=s) (a:=a)) x=f x := by
  simp only [C.coefficient,Finset.prod_empty,Finset.univ_eq_empty,Finset.prod_empty,mul_one,
    Fintype.sum_unique]
  simp only [A.family,A.newLabel,Nat.lt_irrefl,dite_false]
  rw [cast_apply]
  congr 1

theorem row_central (h : Signature.CentralSupport f) :
    Signature.CentralSupport (A.family G f (A.newLabel (s:=s))) := by
  have he := congrArg (fun z : AnySignature AlgebraicComplex => Signature.CentralSupport z.2)
    (A.family_new G f)
  exact he.mpr h

variable (B : Network AlgebraicComplex 2) (BL : Labelling B.shape s 1 a)
variable (hL : LabelledNetwork.Exact G B BL) (hN : ∀e,B.edge e=Signature.disequality)
variable (hE : Signature.CentralSupport B.denote)

include hE in
theorem normalized_central (u : Fin 2→Bool) : Signature.CentralSupport (P.normalized B u) := by
  intro x hx
  simp only [P.normalized,hE x hx,zero_div]

include hL hN hE in
/-- A concrete one-sided binary graph removes unbounded literal pins. -/
theorem zero_sided (u : Fin 2→Bool) (hu : B.denote u≠0)
    (hz : (B.denote ![false,true]≠0 ∧ B.denote ![true,false]=0) ∨
      (B.denote ![false,true]=0 ∧ B.denote ![true,false]≠0)) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) := by
  apply P.pull_elimination G B BL hL hN u hu
  refine ⟨GeneralEOZeroSidedCapConsumers.elimination
    (A.family G (P.normalized B u)) A.newLabel (ports (s:=s) (a:=a))
    (row_central G _ (normalized_central B hE u)) ?_⟩
  unfold Z.Coefficients
  rw [coefficient,coefficient]
  rcases hz with ⟨hp,hq⟩|⟨hp,hq⟩
  · exact Or.inl ⟨div_ne_zero hp hu,by simp [P.normalized,hq]⟩
  · exact Or.inr ⟨by simp [P.normalized,hp],div_ne_zero hq hu⟩

def exponent : ℕ := F.exponent (A.family G (P.normalized B ![false,true]))

include hL hN hE in
/-- Finite nonresonance is checked on the actual graph's two coefficients. -/
theorem nonresonant (hp : B.denote ![false,true]≠0) (hq : B.denote ![true,false]≠0)
    (hr : B.denote ![false,true]^exponent G B≠B.denote ![true,false]^exponent G B) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) := by
  apply P.pull_elimination G B BL hL hN ![false,true] hp
  refine ⟨GeneralEONonARSPinningConsumers.elimination
    (A.family G (P.normalized B ![false,true])) A.newLabel (ports (s:=s) (a:=a))
    (row_central G _ (normalized_central B hE ![false,true])) ?_⟩
  unfold F.Coefficients
  rw [coefficient,coefficient]
  refine ⟨div_ne_zero hp hp,div_ne_zero hq hp,?_⟩
  intro he
  apply hr
  exact (div_left_inj' (pow_ne_zero (exponent G B) hp)).mp
    (by simpa only [P.normalized,div_pow,exponent] using he)


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOGeneralPhaseBinaryPins
