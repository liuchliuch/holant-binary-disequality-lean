import Holant.Dihedral.CompatibleClosure.ProductExtraction
import Holant.Dihedral.SectorRuling.MatchingSupport
import Mathlib.Data.Fintype.Pi

/-! A shared deletion chart for two matchings on four original ports. -/
namespace Holant.Dihedral.SixPortBase

open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

/-- The two deleted ports belong to different matching edges. The last bit
records which surviving endpoint belongs to the first deleted endpoint. -/
def Crossed (p : (Fin 2 × Bool) ≃ Fin 4) (c : (Bool × Bool) ≃ Fin 4) : Prop :=
  ∃ e f : Fin 2, e ≠ f ∧ ∃ b d s : Bool,
    c (false,false) = p (e,b) ∧ c (false,true) = p (f,d) ∧
    c (true,s) = p (e,!b) ∧ c (true,!s) = p (f,!d)

/-- Two possible bipartitions suffice after fixing one matching's chart. -/
def crossingSlots (t : Bool) : (Bool × Bool) ≃ (Fin 2 × Bool) where
  toFun z := (finTwoEquiv.symm z.2,z.1 ^^ (z.2 && t))
  invFun z := (z.2 ^^ (finTwoEquiv z.1 && t),finTwoEquiv z.1)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by rintro ⟨a,b⟩; simp

private theorem crossingSlots_first (t : Bool) :
    crossingSlots t (false,false) = (0,false) := by cases t <;> rfl
private theorem crossingSlots_second (t : Bool) :
    crossingSlots t (false,true) = (1,t) := by cases t <;> rfl
private theorem crossingSlots_third (t : Bool) :
    crossingSlots t (true,false) = (0,true) := by cases t <;> rfl
private theorem crossingSlots_fourth (t : Bool) :
    crossingSlots t (true,true) = (1,!t) := by cases t <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem common_crossing_finite :
    ∀ g : (Fin 2 × Bool) → (Fin 2 × Bool), Function.Injective g →
    ∃ t : Bool, ∃ e f : Fin 2, e ≠ f ∧ ∃ b d s : Bool,
      crossingSlots t (false,false) = g (e,b) ∧
      crossingSlots t (false,true) = g (f,d) ∧
      crossingSlots t (true,s) = g (e,!b) ∧
      crossingSlots t (true,!s) = g (f,!d) := by
  decide

/-- The common chart is an equivalence onto the original four ports. Both
matchings cross its deleted/surviving split; their survivor orders may differ. -/
theorem exists_common_crossing_chart (p q : (Fin 2 × Bool) ≃ Fin 4) :
    ∃ c : (Bool × Bool) ≃ Fin 4, Crossed p c ∧ Crossed q c := by
  obtain ⟨t,e,f,hef,b,d,s,h₀,h₁,h₂,h₃⟩ :=
    common_crossing_finite (fun z => p.symm (q z)) (p.symm.injective.comp q.injective)
  refine ⟨(crossingSlots t).trans p,?_,e,f,hef,b,d,s,?_,?_,?_,?_⟩
  · refine ⟨0,1,by decide,false,t,false,?_,?_,?_,?_⟩ <;>
      simp only [Equiv.trans_apply,crossingSlots_first,crossingSlots_second,
        crossingSlots_third,crossingSlots_fourth,Bool.not_false]
  all_goals
    first
    | simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using congrArg p h₀
    | simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using congrArg p h₁
    | simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using congrArg p h₂
    | simpa only [Equiv.trans_apply,Equiv.apply_symm_apply] using congrArg p h₃

/-- Transpose only the literal matrix whose endpoint orientation is reversed. -/
def orientMatrix (b : Bool) (A : Mat) : Mat := if b then Kernel.transpose A else A

private theorem two_factor_product (v : Fin 2 → Scalar) (e f : Fin 2) (hef : e ≠ f) :
    (∏ i, v i) = v e * v f := by
  fin_cases e <;> fin_cases f <;> simp_all [Fin.prod_univ_two,mul_comm]

/-- A crossed matching product is exactly the ordinary fusion input, with a
possible exchange of its surviving coordinates. No coefficient is discarded. -/
theorem product_cross_form (p : (Fin 2 × Bool) ≃ Fin 4)
    (c : (Bool × Bool) ≃ Fin 4) (A : Fin 2 → Mat) (κ : Scalar)
    (e f : Fin 2) (hef : e ≠ f) (b d s : Bool)
    (h₀ : c (false,false) = p (e,b)) (h₁ : c (false,true) = p (f,d))
    (h₂ : c (true,s) = p (e,!b)) (h₃ : c (true,!s) = p (f,!d))
    (x : Fin 4 → Bool) :
    productValue p A κ x = κ *
      orientMatrix (!b) (A e) (x (c (true,s))) (x (c (false,false))) *
      orientMatrix d (A f) (x (c (false,true))) (x (c (true,!s))) := by
  rw [productValue,two_factor_product _ e f hef]
  rw [h₀,h₁,h₂,h₃]
  cases b <;> cases d <;> simp [orientMatrix,Kernel.transpose,mul_assoc]

/-- The witnesses can be obtained directly from the shared-chart predicate. -/
theorem Crossed.product_form {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) :
    ∃ e f : Fin 2, e ≠ f ∧ ∃ b d s : Bool,
      ∀ x : Fin 4 → Bool, productValue p A κ x = κ *
        orientMatrix (!b) (A e) (x (c (true,s))) (x (c (false,false))) *
        orientMatrix d (A f) (x (c (false,true))) (x (c (true,!s))) := by
  obtain ⟨e,f,hef,b,d,s,h₀,h₁,h₂,h₃⟩ := h
  exact ⟨e,f,hef,b,d,s,product_cross_form p c A κ e f hef b d s h₀ h₁ h₂ h₃⟩

/-- Closing the common deleted pair is an ordinary fusion of the two
oriented literal factors, evaluated in their own survivor order. -/
theorem Crossed.close_product {p : (Fin 2 × Bool) ≃ Fin 4}
    {c : (Bool × Bool) ≃ Fin 4} (h : Crossed p c)
    (A : Fin 2 → Mat) (κ : Scalar) :
    ∃ e f : Fin 2, e ≠ f ∧ ∃ b d s : Bool,
      ∀ (C : Mat) (x : Fin 4 → Bool),
        (∑ a : Bool, ∑ k : Bool, C a k * productValue p A κ
          (insertPair (c (false,false)) (c (false,true)) a k x)) =
        κ * fuse C (orientMatrix (!b) (A e)) (orientMatrix d (A f))
          (x (c (true,s))) (x (c (true,!s))) := by
  obtain ⟨e,f,hef,b,d,s,hp⟩ := h.product_form A κ
  refine ⟨e,f,hef,b,d,s,?_⟩
  intro C x
  have hneq : c (false,false) ≠ c (false,true) :=
    fun hh => by have hh' := c.injective hh; cases hh'
  have hs (a k t : Bool) :
      insertPair (c (false,false)) (c (false,true)) a k x (c (true,t)) =
        x (c (true,t)) := by
    apply insertPair_other
    · intro hh; have hh' := congrArg Prod.fst (c.injective hh); cases hh'
    · intro hh; have hh' := congrArg Prod.fst (c.injective hh); cases hh'
  have hp' (a k : Bool) := hp (insertPair (c (false,false)) (c (false,true)) a k x)
  simp only [insertPair_first hneq,insertPair_second,hs] at hp'
  simp only [hp',fuse,Signature.connect,Fintype.sum_bool]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
private theorem matching_projection_finite :
    ∀ α : Fin 2 → Bool, ∀ u v : Fin 2 × Bool, u ≠ v →
      (Finset.univ.image (fun z : Fin 2 → Bool =>
        ((if u.2 then z u.1 ^^ α u.1 else z u.1),
         (if v.2 then z v.1 ^^ α v.1 else z v.1)))).card =
        if u.1 = v.1 then 2 else 4 := by
  decide

/-- Projecting the four monomial matching words onto any two original ports
has two values for one original edge and four values for two different edges. -/
theorem matchingWord_projection_card (p : (Fin 2 × Bool) ≃ Fin 4)
    (α : Fin 2 → Bool) (u v : Fin 4) (huv : u ≠ v) :
    (Finset.univ.image (fun z : Fin 2 → Bool =>
      (SectorRuling.matchingWord p α z u,SectorRuling.matchingWord p α z v))).card =
      if (p.symm u).1 = (p.symm v).1 then 2 else 4 := by
  exact matching_projection_finite α (p.symm u) (p.symm v)
    (fun h => huv (p.symm.injective h))

/-- The support projection is never a singleton or a three-point set. -/
theorem matchingWord_projection_two_or_four (p : (Fin 2 × Bool) ≃ Fin 4)
    (α : Fin 2 → Bool) (u v : Fin 4) (huv : u ≠ v) :
    (Finset.univ.image (fun z : Fin 2 → Bool =>
      (SectorRuling.matchingWord p α z u,SectorRuling.matchingWord p α z v))).card = 2 ∨
    (Finset.univ.image (fun z : Fin 2 → Bool =>
      (SectorRuling.matchingWord p α z u,SectorRuling.matchingWord p α z v))).card = 4 := by
  rw [matchingWord_projection_card p α u v huv]
  split_ifs <;> simp

end Holant.Dihedral.SixPortBase
