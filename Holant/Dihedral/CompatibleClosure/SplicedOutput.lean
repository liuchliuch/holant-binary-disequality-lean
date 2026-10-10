import Holant.Dihedral.CompatibleClosure.SelectedEdges
import Holant.Dihedral.CompatibleClosure.PhysicalPair

/-! The literal contracted product is tied to the computed surviving perfect
matching: one new original-neighbor edge and every untouched original edge. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Dihedral.EndpointParallelogram

variable {n r : ℕ}

theorem selected_untouched (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n) (d : Fin r)
    (he : d ≠ (p.symm u).1) (hf : d ≠ (p.symm v).1) (b : Bool) :
    selectedPorts p u v (d,b) = p (d,b) := by
  simp [selectedPorts,flipSlots,selectMask,he,hf]

/-- Exact coefficient formula on the new original-neighbor edge and all
untouched original factors. It is derived from the complete source product. -/
theorem spliced_product_value (p : (Fin r × Bool) ≃ Fin n) (A : Fin r → Mat) (κ : Scalar)
    (u v : Fin n) (huv : u ≠ v) (hd : (Pairing.ofPorts p).mate u ≠ v) (C : Mat) (x : Fin n → Bool) :
    let e := (p.symm u).1
    let f := (p.symm v).1
    let B := fun j => if selectMask p u v j then Kernel.transpose (A j) else A j
    (∑ a : Bool, ∑ b : Bool, C a b * productValue p A κ (insertPair u v a b x)) =
      fuse C (B e) (B f) (x ((Pairing.ofPorts p).mate u)) (x ((Pairing.ofPorts p).mate v)) *
        (κ * ∏ d ∈ (Finset.univ.erase e).erase f, A d (x (p (d,false))) (x (p (d,true)))) := by
  dsimp only
  let B := fun j => if selectMask p u v j then Kernel.transpose (A j) else A j
  have hp : productValue (selectedPorts p u v) B κ = productValue p A κ := reorient_product p A κ _
  have hef := different_edge_indices p u v huv hd
  have hh := close_product_two (selectedPorts p u v) B κ (p.symm u).1 (p.symm v).1 hef C x
  obtain ⟨hu,hv⟩ := selected_endpoints p u v huv hd
  obtain ⟨ha,hb⟩ := selected_neighbors p u v huv hd
  rw [hp,hu,hv,ha,hb] at hh
  rw [hh]
  congr 2
  apply Finset.prod_congr rfl
  intro d hmem
  have he : d ≠ (p.symm u).1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).1
  have hf : d ≠ (p.symm v).1 := (Finset.mem_erase.mp hmem).1
  simp [B,selectMask,he,hf,selected_untouched p u v d he hf]

/-- Every unchanged product factor is literally an edge in the computed
remaining matching, in both orientations. -/
theorem spliced_old_edge (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n) (huv : u ≠ v)
    (hd : (Pairing.ofPorts p).mate u ≠ v) (d : Fin r)
    (he : d ≠ (p.symm u).1) (hf : d ≠ (p.symm v).1)
    (b : Bool) (x : Remaining u v) (hx : x.val = p (d,b)) :
    ((spliceMatching (Pairing.ofPorts p) u v huv hd).mate x).val = p (d,!b) := by
  have ha : x.val ≠ (Pairing.ofPorts p).mate u := by
    rw [hx]
    intro h
    exact he (congrArg Prod.fst (p.injective h))
  have hb : x.val ≠ (Pairing.ofPorts p).mate v := by
    rw [hx]
    intro h
    exact hf (congrArg Prod.fst (p.injective h))
  rw [splice_unaffected _ _ _ _ _ x ha hb,hx]
  simp only [Pairing.ofPorts,Equiv.symm_apply_apply]

/-- The new fused product factor is the actual replacement edge between the
two original opposite endpoints. -/
theorem spliced_new_edge (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n) (huv : u ≠ v)
    (hd : (Pairing.ofPorts p).mate u ≠ v) (x : Remaining u v)
    (hx : x.val = (Pairing.ofPorts p).mate u) :
    ((spliceMatching (Pairing.ofPorts p) u v huv hd).mate x).val = (Pairing.ofPorts p).mate v :=
  splice_connects _ _ _ _ _ x hx

/-- These factors exhaust the computed remaining matching: every surviving
original port is a fused endpoint or belongs to one untouched original factor. -/
theorem spliced_edges_exhaust (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n)
    (x : Remaining u v) :
    x.val = (Pairing.ofPorts p).mate u ∨ x.val = (Pairing.ofPorts p).mate v ∨
      ∃ d b, d ≠ (p.symm u).1 ∧ d ≠ (p.symm v).1 ∧ x.val = p (d,b) := by
  by_cases he : (p.symm x.val).1 = (p.symm u).1
  · left
    by_contra hn
    exact (different_edge_indices p u x.val (Ne.symm x.property.1) (Ne.symm hn)) he.symm
  by_cases hf : (p.symm x.val).1 = (p.symm v).1
  · right; left
    by_contra hn
    exact (different_edge_indices p v x.val (Ne.symm x.property.2) (Ne.symm hn)) hf.symm
  · exact Or.inr (Or.inr ⟨(p.symm x.val).1,(p.symm x.val).2,he,hf,(p.apply_symm_apply x.val).symm⟩)

/-- Direct physical output bridge: the second actual output in a PhysicalPair
has exactly the spliced original matching product, with its recorded multiplier. -/
theorem PhysicalPair.spliced_factorization {m n r : ℕ} {F : SignatureFamily Scalar}
    {G : ActualRepresentatives F m} {q₀ : Signature Scalar (n+2)}
    (p : (Fin r × Bool) ≃ Fin (n+2)) (A : Fin r → Mat) (κ : Scalar)
    {order : Equiv.Perm (Fin (n+2))} {γ : Bool} {t : {t : Scalar // Roots m t}}
    (P : PhysicalPair F G q₀ (productValue p A κ) order γ t)
    (u v : Fin (n+2)) (huv : u ≠ v) (hd : (Pairing.ofPorts p).mate u ≠ v)
    (horder₀ : order 0 = u) (horder₁ : order 1 = v) (x : Fin (n+2) → Bool) :
    let e := (p.symm u).1
    let f := (p.symm v).1
    let B := fun j => if selectMask p u v j then Kernel.transpose (A j) else A j
    ((P.circle₁*G.multiplier γ t) • close γ t.val (Tensor.reindex order.symm (productValue p A κ)))
      (fun i => x (order i.succ.succ)) =
      (P.circle₁*G.multiplier γ t) *
        (fuse (M γ t.val) (B e) (B f) (x ((Pairing.ofPorts p).mate u)) (x ((Pairing.ofPorts p).mate v)) *
          (κ * ∏ d ∈ (Finset.univ.erase e).erase f, A d (x (p (d,false))) (x (p (d,true))))) := by
  dsimp only
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [← full_close_order,horder₀,horder₁,spliced_product_value p A κ u v huv hd]

end Holant.Dihedral.CompatibleClosure
