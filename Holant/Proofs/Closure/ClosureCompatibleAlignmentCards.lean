import Holant.Proofs.Closure.ClosureCompatibleAlignmentMatching

/-! Constructing the frozen CompatibleCards data from two selected literal
card products.  The matching orientation and full physical representative
scalars are derived.  Common per-edge support parity is an explicit local
domain: it is not inferred from equality of matching involutions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.EndpointParallelogram

theorem pairPorts_last_false (r : ℕ) :
    pairPorts r (Fin.last r,false) = ⟨2*r,by omega⟩ := by
  apply Fin.ext
  simp only [pairPorts_val,Fin.val_last,Bool.false_eq_true,ite_false,Nat.add_zero]

theorem pairPorts_last_true (r : ℕ) :
    pairPorts r (Fin.last r,true) = ⟨2*r+1,by omega⟩ := by
  apply Fin.ext
  simp only [pairPorts_val,Fin.val_last,ite_true]

def residualLayout {r : ℕ} (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (e : Fin (r+1)) : Equiv.Perm (Fin (2*r+2)) :=
  (pairPorts r).symm.trans
    ((Equiv.prodCongr (Equiv.swap (Fin.last r) e) (Equiv.refl Bool)).trans p)

theorem residualLayout_last_false {r : ℕ}
    (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1)) :
    residualLayout p e ⟨2*r,by omega⟩ = p (e,false) := by
  rw [← pairPorts_last_false]
  simp [residualLayout]

theorem residualLayout_last_true {r : ℕ}
    (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1)) :
    residualLayout p e ⟨2*r+1,by omega⟩ = p (e,true) := by
  rw [← pairPorts_last_true]
  simp [residualLayout]

/-- The canonical last-edge presentation is proved from the full original
product; no caller-supplied ordered coefficient-product identity is used. -/
theorem residualLayout_product {r : ℕ}
    (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (e : Fin (r+1))
    (A : Fin (r+1) → Mat) (κ : Scalar) :
    Tensor.reindex (residualLayout p e).symm (productValue p A κ) =
      κ • product r (fun j => A ((Equiv.swap (Fin.last r) e) j.castSucc)) (A e) := by
  funext x
  simp only [Tensor.reindex,productValue,Pi.smul_apply,smul_eq_mul]
  rw [← Equiv.prod_comp (Equiv.swap (Fin.last r) e)
    (fun j => A j (x ((residualLayout p e).symm (p (j,false))))
      (x ((residualLayout p e).symm (p (j,true)))))]
  have identities (j : Fin (r+1)) (b : Bool) :
      (residualLayout p e).symm (p ((Equiv.swap (Fin.last r) e) j,b)) = pairPorts r (j,b) := by
    simp [residualLayout]
  simp only [identities]
  rw [← product_eq_full r (fun j => A ((Equiv.swap (Fin.last r) e) j))]
  simp only [Equiv.swap_apply_left]

def alignedTables {r : ℕ}
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (b : Bool) : Fin (r+1) → Mat :=
  if b then alignedFactor (p false) (p true) (A true) else A false

theorem alignedTables_product {r : ℕ}
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (κ : Bool → Scalar)
    (same : (Pairing.ofPorts (p false)).mate = (Pairing.ofPorts (p true)).mate)
    (b : Bool) :
    productValue (p false) (alignedTables p A b) (κ b) = productValue (p b) (A b) (κ b) := by
  cases b
  · rfl
  · exact aligned_product (p false) (p true) same (A true) (κ true)

/-- The exact two selected actual cards, after internally computed edge
alignment, give a real CompatibleCards instance.  The designated original
residual pair is (0,1), hence the ancestor's protected pair is literally (2,3).
All other edges retain their computed source table and shared support parity. -/
def fromSelectedProducts {m r : ℕ} {F : SignatureFamily Scalar}
    (G : ActualRepresentatives F m) (f : Signature Scalar (2*r+4))
    (actual : Gadget.Realizes F .disequality f)
    (sector : Bool → Bool) (phase : Bool → {t : Scalar // Roots m t})
    (p : Bool → (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A : Bool → Fin (r+1) → Mat) (κ : Bool → Scalar)
    (nonzero : ∀ b,κ b ≠ 0)
    (equation : ∀ b,Signature.contract (M (sector b) (phase b).val) f =
      productValue (p b) (A b) (κ b))
    (same : (Pairing.ofPorts (p false)).mate = (Pairing.ofPorts (p true)).mate)
    (e : Fin (r+1)) (first : p false (e,false) = 0) (second : p false (e,true) = 1)
    (parity : Fin (r+1) → Bool)
    (sameParity : ∀ b j,HasParity (parity j) (alignedTables p A b j)) :
    CompatibleCards G f := by
  let layout := residualLayout (p false) e
  let edgeOrder := Equiv.swap (Fin.last r) e
  have physical (b : Bool) : ∃ c : Scalar,c ≠ 0 ∧
      Gadget.Realizes F .disequality
        (c • physicalCard r (Tensor.reindex (ancestorOrder r layout).symm f)
          (G.binary (sector b) (phase b))) := by
    obtain ⟨c,_choice,hc,hr⟩ := realizes_native_connection F f
      (G.binary (sector b) (phase b)) actual (G.actual (sector b) (phase b))
    refine ⟨c,hc,?_⟩
    rw [ordered_physicalCard]
    exact realizes_reindex F .disequality _ hr layout
  choose circle circle_nonzero circle_actual using physical
  refine {
    order := ancestorOrder r layout
    deleted_first := ?_
    deleted_second := ?_
    protected_first := ?_
    protected_second := ?_
    sector := sector
    phase := phase
    actualScalar := circle
    actualScalar_ne_zero := circle_nonzero
    originalScalar := fun b => (circle b*G.multiplier (sector b) (phase b))*κ b
    originalScalar_ne_zero := fun b => mul_ne_zero
      (mul_ne_zero (circle_nonzero b) (G.multiplier_ne_zero (sector b) (phase b))) (nonzero b)
    complement := fun b j => alignedTables p A b (edgeOrder j.castSucc)
    edgeFactor := fun b => alignedTables p A b e
    parity := fun j => parity (edgeOrder j.castSucc)
    complement_parity := fun b j => sameParity b _
    protectedParity := parity e
    protected_parity := fun b => sameParity b e
    actual := circle_actual
    equation := ?_
  }
  · simp only [ancestorOrder,Equiv.trans_apply,shuffleDeleted_p0]
    rfl
  · simp only [ancestorOrder,Equiv.trans_apply,shuffleDeleted_p1]
    rfl
  · simp only [ancestorOrder,Equiv.trans_apply,shuffleDeleted_e0]
    change (layout ⟨2*r,by omega⟩).succ.succ = 2
    rw [residualLayout_last_false,first]
    rfl
  · simp only [ancestorOrder,Equiv.trans_apply,shuffleDeleted_e1]
    change (layout ⟨2*r+1,by omega⟩).succ.succ = 3
    rw [residualLayout_last_true,second]
    rfl
  · intro b
    rw [physicalCard_normalization,smul_smul,ordered_card,equation b]
    rw [← alignedTables_product p A κ same b]
    rw [residualLayout_product]
    rw [smul_smul]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
