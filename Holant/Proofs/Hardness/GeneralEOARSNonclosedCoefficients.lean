import Holant.Proofs.Hardness.GeneralEOARSNonclosedMating
import Holant.Proofs.Hardness.GeneralEOARSNonclosedGram

/-! Exact complex Gram coefficients of the literal mating network. ARS is
allowed up to any nonzero scalar, whose unit phase is derived internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedCoefficients
open Holant
open scoped BigOperators
namespace F
export SelfDualPinObstruction (flip flip_flip flipEquiv)
end F
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace G
export GeneralEOARSNonclosedGram (rowMass rowInner saturated_support)
end G
namespace M
export GeneralEOARSNonclosedMating (output network denote)
end M
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def row (f : Signature ℂ (n+2)) (a b : Bool) : (Fin n → Bool) → ℂ :=
  fun z => f (O.word a b z)

theorem phase (f : Signature ℂ n) (hf : GeneralEOARSBoundary.ARSUpToScale f) :
    ∃ t : ℂ, ‖t‖=1 ∧ ∀ x, f (F.flip x)=t * star (f x) := by
  obtain ⟨c,hc,g,hg,rfl⟩ := hf
  refine ⟨c / star c,?_,?_⟩
  · rw [norm_div,norm_star,div_self (norm_ne_zero_iff.mpr hc)]
  · intro x
    change c * g (F.flip x) = c / star c * star (c * g x)
    have hh : g (F.flip x)=star (g x) := hg x
    rw [hh,star_mul]
    field_simp [star_ne_zero.mpr hc]
    exact (mul_div_cancel_right₀ _ (star_ne_zero.mpr hc)).symm

theorem flip_word (a b : Bool) (z : Fin n → Bool) :
    F.flip (O.word a b z)=O.word (!a) (!b) (F.flip z) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i <;> rfl

theorem row_mass_nonneg (u : (Fin n → Bool) → ℂ) : 0 ≤ G.rowMass u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem row_inner_self (u : (Fin n → Bool) → ℂ) : G.rowInner u u=(G.rowMass u : ℂ) := by
  simp only [G.rowInner,G.rowMass,Complex.ofReal_sum,Complex.ofReal_pow,Complex.star_def,
    Complex.mul_conj']

theorem output_phase (f : Signature ℂ (n+2)) (t : ℂ)
    (hf : ∀ x, f (F.flip x)=t * star (f x)) (x : Fin 4 → Bool) :
    M.output f x=t * G.rowInner (row f (x 0) (x 1)) (row f (!(x 2)) (!(x 3))) := by
  unfold M.output G.rowInner row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have hh := hf (O.word (!(x 2)) (!(x 3)) z)
  rw [flip_word] at hh
  simp only [Bool.not_not] at hh
  change f (O.word (x 2) (x 3) (fun k => !(z k))) = _ at hh
  rw [hh]
  ring

theorem diagonal_norm (f : Signature ℂ (n+2))
    (hf : GeneralEOARSBoundary.ARSUpToScale f) (a b : Bool) :
    ‖M.output f ![a,b,!a,!b]‖=G.rowMass (row f a b) := by
  obtain ⟨t,ht,hf⟩ := phase f hf
  rw [output_phase f t hf]
  change ‖t * G.rowInner (row f a b) (row f (!(!a)) (!(!b)))‖ = _
  simp only [Bool.not_not]
  rw [row_inner_self,norm_mul,ht,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (row_mass_nonneg _)]

theorem cross_norm (f : Signature ℂ (n+2))
    (hf : GeneralEOARSBoundary.ARSUpToScale f) :
    ‖M.output f ![false,true,false,true]‖=‖G.rowInner (row f false true) (row f true false)‖ := by
  obtain ⟨t,ht,hf⟩ := phase f hf
  rw [output_phase f t hf]
  simp [norm_mul,ht]

theorem cross_complement_norm (f : Signature ℂ (n+2))
    (hf : GeneralEOARSBoundary.ARSUpToScale f) :
    ‖M.output f ![true,false,true,false]‖=‖M.output f ![false,true,false,true]‖ := by
  obtain ⟨t,ht,hp⟩ := phase f hf
  rw [output_phase f t hp,output_phase f t hp]
  simp only [norm_mul,ht,one_mul]
  have hh : star (G.rowInner (row f false true) (row f true false))=
      G.rowInner (row f true false) (row f false true) := by
    simp only [G.rowInner,star_sum,star_mul,star_star]
  change ‖G.rowInner (row f true false) (row f false true)‖=
    ‖G.rowInner (row f false true) (row f true false)‖
  rw [←hh,norm_star]

theorem complementary_mass (f : Signature ℂ (n+2))
    (hf : GeneralEOARSBoundary.ARSUpToScale f) (a b : Bool) :
    G.rowMass (row f (!a) (!b))=G.rowMass (row f a b) := by
  unfold G.rowMass row
  apply Fintype.sum_equiv (F.flipEquiv (Fin n))
  intro z
  have hh := GeneralEOARSBoundary.opposite_norm f hf (O.word a b (F.flip z))
  rw [flip_word,F.flip_flip] at hh
  rw [hh]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedCoefficients
