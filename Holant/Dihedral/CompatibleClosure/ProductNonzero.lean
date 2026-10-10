import Holant.Dihedral.CompatibleClosure.ProductExtraction

/-! Nonzero residual products and actual closures are derived from the original
monomial factors, including arbitrary representative multipliers. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

variable {ι : Type*} [DecidableEq ι] {r : ℕ}

def supportedWord (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat)
    (hA : ∀ e, IsMonomial (A e)) : ι → Bool := fun i =>
  if (p.symm i).2 then Classical.choose ((hA (p.symm i).1).unique_row false) else false

theorem supportedWord_factor (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat)
    (hA : ∀ e, IsMonomial (A e)) (e : Fin r) :
    A e (supportedWord p A hA (p (e,false))) (supportedWord p A hA (p (e,true))) ≠ 0 := by
  simp only [supportedWord,Equiv.symm_apply_apply,Bool.false_eq_true,ite_false,ite_true]
  exact (Classical.choose_spec ((hA e).unique_row false)).1

theorem productValue_nonzero (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat)
    (hA : ∀ e, IsMonomial (A e)) {κ : Scalar} (hκ : κ ≠ 0) : productValue p A κ ≠ 0 := by
  intro hh
  have hn : productValue p A κ (supportedWord p A hA) ≠ 0 :=
    mul_ne_zero hκ (Finset.prod_ne_zero_iff.mpr (fun e _ => supportedWord_factor p A hA e))
  exact hn (congrFun hh _)

/-- Closing a compatible edge remains nonzero whenever the actual selected
trace is nonzero; all residual coefficient factors are derived from the input. -/
theorem close_product_edge_nonzero (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat)
    (hA : ∀ e, IsMonomial (A e)) {κ : Scalar} (hκ : κ ≠ 0) (e : Fin r) (C : Mat)
    (ht : trace (A e) C ≠ 0) :
    (fun x => ∑ a : Bool, ∑ b : Bool, C a b *
      productValue p A κ (insertPair (p (e,false)) (p (e,true)) a b x)) ≠ 0 := by
  intro hh
  have he := congrFun hh (supportedWord p A hA)
  rw [close_product_edge] at he
  exact (mul_ne_zero ht (mul_ne_zero hκ
    (Finset.prod_ne_zero_iff.mpr (fun d _ => supportedWord_factor p A hA d)))) he

/-- Cross-closing two distinct factors is nonzero for every nonsingular
monomial connection; its internal sum has a unique surviving lift. -/
theorem close_product_two_nonzero (p : (Fin r × Bool) ≃ ι) (A : Fin r → Mat)
    (hA : ∀ e, IsMonomial (A e)) {κ : Scalar} (hκ : κ ≠ 0)
    (e f : Fin r) (hef : e ≠ f) (C : Mat) (hC : IsMonomial C) :
    (fun x => ∑ a : Bool, ∑ b : Bool, C a b *
      productValue p A κ (insertPair (p (e,true)) (p (f,false)) a b x)) ≠ 0 := by
  have hF : IsMonomial (fuse C (A e) (A f)) := by
    rw [fuse_eq_mul]
    exact ((hA e).mul hC).mul (hA f)
  obtain ⟨b,hb,_⟩ := hF.unique_row false
  let x := Function.update (supportedWord p A hA) (p (f,true)) b
  have her : x (p (e,false)) = false := by
    have hne : p (e,false) ≠ p (f,true) := fun h => hef (congrArg Prod.fst (p.injective h))
    simp [x,hne,supportedWord]
  have hfs : x (p (f,true)) = b := by simp [x]
  have hrest : (∏ d ∈ (Finset.univ.erase e).erase f,
      A d (x (p (d,false))) (x (p (d,true)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro d hd
    have hdf : d ≠ f := (Finset.mem_erase.mp hd).1
    have hne (z : Bool) : p (d,z) ≠ p (f,true) := fun h => hdf (congrArg Prod.fst (p.injective h))
    simpa only [x,Function.update_of_ne (hne false),Function.update_of_ne (hne true)] using
      supportedWord_factor p A hA d
  intro hh
  have he := congrFun hh x
  rw [close_product_two p A κ e f hef,her,hfs] at he
  exact (mul_ne_zero hb (mul_ne_zero hκ hrest)) he

end Holant.Dihedral.CompatibleClosure
