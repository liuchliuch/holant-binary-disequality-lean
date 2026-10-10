import Holant.Dihedral.SixPortBase.CrossingOriginal

/-! Unique internal lifts expressed on the actual original four-port product.
The proof handles the monomial/monomial and monomial/singleton crossings with
the same coefficient identity. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase.Crossing
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false

theorem crossing_deleted_ne (c : (Bool × Bool) ≃ Fin 4) :
    c (false,false) ≠ c (false,true) :=
  fun h => (by decide : (false,false) ≠ (false,true)) (c.injective h)

theorem crossing_insert_survivor (c : (Bool × Bool) ≃ Fin 4)
    (i j u v s : Bool) :
    insertPair (c (false,false)) (c (false,true)) i j (survivorWord c u v)
      (c (true,s)) = if s then v else u := by
  rw [insertPair_other]
  · exact survivorWord_apply c true s u v
  · intro h
    have h' := congrArg Prod.fst (c.injective h)
    cases h'
  · intro h
    have h' := congrArg Prod.fst (c.injective h)
    cases h'

/-- One original monomial factor and the phase-one parity kernel already
force both deleted bits. The second original factor can be arbitrary. -/
theorem original_contract_unique_lift {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar)
    (hA : IsMonomial (A 0) ∨ IsMonomial (A 1)) (hκ : κ ≠ 0)
    (γ u v : Bool) :
    originalContract c γ (productValue p A κ) u v ≠ 0 ↔
      ∃! ij : PairWord,M γ 1 ij.1 ij.2 * productValue p A κ
        (insertPair (c (false,false)) (c (false,true)) ij.1 ij.2
          (survivorWord c u v)) ≠ 0 := by
  obtain ⟨e,f,hef,b,d,s,hp⟩ := h.product_form A κ
  let L := orientMatrix (!b) (A e)
  let R := orientMatrix d (A f)
  let a := if s then v else u
  let z := if s then u else v
  have hterm (i j : Bool) : M γ 1 i j * productValue p A κ
      (insertPair (c (false,false)) (c (false,true)) i j (survivorWord c u v)) =
      κ*(M γ 1 i j*(L a i*R j z)) := by
    rw [hp,insertPair_first (crossing_deleted_ne c),insertPair_second,
      crossing_insert_survivor,crossing_insert_survivor]
    dsimp [L,R,a,z]
    cases s <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,
      ite_false,ite_true] <;> ring
  have hsum : originalContract c γ (productValue p A κ) u v=κ*contract γ L R a z := by
    simp only [originalContract,hterm,contract_sum,Fintype.sum_bool]
    ring
  have hmono : IsMonomial (A e) ∨ IsMonomial (A f) := by
    fin_cases e <;> fin_cases f
    · exact False.elim (hef rfl)
    · exact hA
    · exact hA.symm
    · exact False.elim (hef rfl)
  have hu : contract γ L R a z ≠ 0 ↔ ∃! ij : PairWord,
      M γ 1 ij.1 ij.2*(L a ij.1*R ij.2 z) ≠ 0 := by
    rcases hmono with he|hf
    · exact contract_unique_lift_left γ (oriented_monomial _ he) R a z
    · exact contract_unique_lift_right γ L (oriented_monomial _ hf) a z
  rw [hsum,mul_ne_zero_iff,and_iff_right hκ,hu]
  have he (ij : PairWord) : M γ 1 ij.1 ij.2 * productValue p A κ
      (insertPair (c (false,false)) (c (false,true)) ij.1 ij.2 (survivorWord c u v)) ≠ 0 ↔
      M γ 1 ij.1 ij.2*(L a ij.1*R ij.2 z) ≠ 0 := by
    rw [hterm,mul_ne_zero_iff,and_iff_right hκ]
  constructor
  · rintro ⟨ij,hij,hi⟩
    exact ⟨ij,(he ij).mpr hij,fun kl hk => hi kl ((he kl).mp hk)⟩
  · rintro ⟨ij,hij,hi⟩
    exact ⟨ij,(he ij).mp hij,fun kl hk => hi kl ((he kl).mpr hk)⟩

theorem original_pp_unique_lift {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : ∀ e,IsMonomial (A e)) (hκ : κ ≠ 0)
    (γ u v : Bool) :
    originalContract c γ (productValue p A κ) u v ≠ 0 ↔
      ∃! ij : PairWord,M γ 1 ij.1 ij.2 * productValue p A κ
        (insertPair (c (false,false)) (c (false,true)) ij.1 ij.2
          (survivorWord c u v)) ≠ 0 :=
  original_contract_unique_lift h A κ (Or.inl (hA 0)) hκ γ u v

theorem original_pc_unique_lift {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) (hA : OnePointProduct A) (hκ : κ ≠ 0)
    (γ u v : Bool) :
    originalContract c γ (productValue p A κ) u v ≠ 0 ↔
      ∃! ij : PairWord,M γ 1 ij.1 ij.2 * productValue p A κ
        (insertPair (c (false,false)) (c (false,true)) ij.1 ij.2
          (survivorWord c u v)) ≠ 0 := by
  apply original_contract_unique_lift h A κ _ hκ γ u v
  rcases hA with ⟨h,_⟩|⟨_,h⟩
  · exact Or.inl h
  · exact Or.inr h

end Holant.Dihedral.SixPortBase.Crossing
