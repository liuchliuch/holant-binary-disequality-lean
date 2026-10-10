import Holant.Dihedral.SixPortBase.CrossingBranches
import Holant.Dihedral.SixPortBase.CrossingLifts
import Holant.Dihedral.CompatibleCoefficientLine.PortAlignment

/-! Exact transport from original distinguished-pair rows to an actual oriented
six-to-four card. The ordered surviving output keeps the original distinguished
pair first, so its two-port projection is the same projection counted in the
P/C obstruction. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase.Crossing
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine Holant.Dihedral.SectorRuling
set_option backward.isDefEq.respectTransparency false

/-- Four output bits, with the original distinguished pair first. -/
def packQuad (x : QuadWord) : Fin 4 → Bool := ![x.1.1,x.1.2,x.2.1,x.2.2]

def packQuadEquiv : QuadWord ≃ (Fin 4 → Bool) where
  toFun := packQuad
  invFun x := ((x 0,x 1),(x 2,x 3))
  left_inv := by rintro ⟨⟨a,b⟩,⟨u,v⟩⟩; rfl
  right_inv := by intro x; funext i; fin_cases i <;> rfl

def packedRows (F : Residual) : Rows := fun w u v => F (packQuad (w,(u,v)))

/-- Standard four-slot order: two deleted ports, then two surviving ports. -/
def quadSlots : (Bool × Bool) ≃ Fin 4 :=
  (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv

private theorem quadSlots_values :
    quadSlots (false,false)=0 ∧ quadSlots (false,true)=1 ∧
    quadSlots (true,false)=2 ∧ quadSlots (true,true)=3 := by decide

def residualOrder (c : (Bool × Bool) ≃ Fin 4) : Equiv.Perm (Fin 4) :=
  quadSlots.symm.trans c

/-- The new leading pair is the selected crossing pair. The next pair is
literally the original distinguished pair, followed by the two residual survivors. -/
def crossingOrder (c : (Bool × Bool) ≃ Fin 4) : Equiv.Perm (Fin 6) :=
  (swapPairs 2).trans (liftPair (residualOrder c))

theorem crossingOrder_ports (c : (Bool × Bool) ≃ Fin 4) :
    crossingOrder c 0=(c (false,false)).succ.succ ∧
    crossingOrder c 1=(c (false,true)).succ.succ ∧
    crossingOrder c 2=0 ∧ crossingOrder c 3=1 ∧
    crossingOrder c 4=(c (true,false)).succ.succ ∧
    crossingOrder c 5=(c (true,true)).succ.succ := by
  have h0 : quadSlots.symm 0=(false,false) := quadSlots.symm_apply_eq.mpr quadSlots_values.1.symm
  have h1 : quadSlots.symm 1=(false,true) := quadSlots.symm_apply_eq.mpr quadSlots_values.2.1.symm
  have h2 : quadSlots.symm 2=(true,false) := quadSlots.symm_apply_eq.mpr quadSlots_values.2.2.1.symm
  have h3 : quadSlots.symm 3=(true,true) := quadSlots.symm_apply_eq.mpr quadSlots_values.2.2.2.symm
  refine ⟨?_,?_,rfl,rfl,?_,?_⟩
  · change (c (quadSlots.symm 0)).succ.succ=(c (false,false)).succ.succ
    rw [h0]
  · change (c (quadSlots.symm 1)).succ.succ=(c (false,true)).succ.succ
    rw [h1]
  · change (c (quadSlots.symm 2)).succ.succ=(c (true,false)).succ.succ
    rw [h2]
  · change (c (quadSlots.symm 3)).succ.succ=(c (true,true)).succ.succ
    rw [h3]

private theorem residual_word (c : (Bool × Bool) ≃ Fin 4) (a b u v : Bool) :
    (fun i => pair a b (![u,v] : Fin 2 → Bool) ((residualOrder c).symm i)) =
      insertPair (c (false,false)) (c (false,true)) a b (survivorWord c u v) := by
  funext i
  obtain ⟨⟨s,t⟩,rfl⟩ := c.surjective i
  simp only [residualOrder,Equiv.symm_trans_apply,Equiv.symm_apply_apply,Equiv.symm_symm]
  cases s
  · cases t
    · rw [insertPair_first (crossing_deleted_ne c),quadSlots_values.1]
      rfl
    · rw [insertPair_second,quadSlots_values.2.1]
      rfl
  · rw [crossing_insert_survivor]
    cases t
    · rw [quadSlots_values.2.2.1]
      rfl
    · rw [quadSlots_values.2.2.2]
      rfl

/-- Word-level transport, before any coefficient or support is considered. -/
theorem crossingOrder_word (c : (Bool × Bool) ≃ Fin 4)
    (a b : Bool) (x : QuadWord) :
    (fun i => pair a b (packQuad x) ((crossingOrder c).symm i)) =
      pair x.1.1 x.1.2
        (insertPair (c (false,false)) (c (false,true)) a b
          (survivorWord c x.2.1 x.2.2)) := by
  rcases x with ⟨⟨w,z⟩,⟨u,v⟩⟩
  have hh := congrArg (fun y : Fin 6 → Bool => fun i => y ((liftPair (residualOrder c)).symm i))
    (word_swapPairs (n:=2) a b w z (![u,v] : Fin 2 → Bool))
  change (fun i => pair a b (packQuad ((w,z),(u,v))) ((crossingOrder c).symm i)) =
    (fun i => pair w z (pair a b (![u,v] : Fin 2 → Bool)) ((liftPair (residualOrder c)).symm i)) at hh
  rw [word_liftPair,residual_word] at hh
  exact hh

/-- The crossing rows are the actual oriented card, with an explicit original
input permutation and a bijective packing of the four output bits. -/
theorem contractSource_eq_actual_close (h : Signature Scalar 6)
    (c : (Bool × Bool) ≃ Fin 4) (γ : Bool) :
    contractSource c γ (fun w y => h (pair w.1 w.2 y)) =
      packedRows (close (n:=4) γ 1 (Tensor.reindex (crossingOrder c).symm h)) := by
  funext w u v
  simp only [contractSource,originalContract,packedRows,close,Tensor.reindex]
  simp_rw [crossingOrder_word]

/-- Packing preserves the actual nonzero coefficients. -/
theorem packedRows_support (F : Residual) :
    (rowSupport (packedRows F)).image packQuad=residualSupport F := by
  classical
  ext y
  simp only [Finset.mem_image,mem_rowSupport,mem_residualSupport]
  constructor
  · rintro ⟨⟨w,z⟩,hx,rfl⟩
    exact hx
  · intro hy
    refine ⟨packQuadEquiv.symm y,?_,packQuadEquiv.apply_symm_apply y⟩
    change F (packQuadEquiv (packQuadEquiv.symm y)) ≠ 0
    simpa using hy

theorem packedRows_support_card (F : Residual) :
    (rowSupport (packedRows F)).card=(residualSupport F).card := by
  classical
  rw [← packedRows_support F]
  exact (Finset.card_image_of_injective _
    (show Function.Injective packQuad from packQuadEquiv.injective)).symm

/-- Projecting the packed rows to their first pair is exactly projection to
the first two physical surviving output ports. -/
theorem packedRows_projection (F : Residual) :
    (rowSupport (packedRows F)).image Prod.fst=
      (residualSupport F).image (fun x => (x 0,x 1)) := by
  classical
  rw [← packedRows_support F,Finset.image_image]
  rfl

@[simp] theorem residualSupport_zero : residualSupport (0 : Residual)=∅ := by
  classical
  ext x
  simp

theorem matching_packedRows_card {m : ℕ} (hm : 0<m) (F : Residual)
    (hF : F=0 ∨ MatchingSample m 2 F) :
    (rowSupport (packedRows F)).card=0 ∨ (rowSupport (packedRows F)).card=4 := by
  rw [packedRows_support_card]
  rcases hF with rfl|⟨p,A,κ,hA,hκ,rfl⟩
  · simp
  · right
    exact product_support_four p A κ (fun e => groupM_isMonomial hm (hA e)) hκ

theorem matching_packedRows_projection {m : ℕ} (hm : 0<m) (F : Residual)
    (hF : F=0 ∨ MatchingSample m 2 F) :
    ((rowSupport (packedRows F)).image Prod.fst).card=0 ∨
    ((rowSupport (packedRows F)).image Prod.fst).card=2 ∨
    ((rowSupport (packedRows F)).image Prod.fst).card=4 := by
  rw [packedRows_projection]
  rcases hF with rfl|⟨p,A,κ,hA,hκ,rfl⟩
  · simp
  · right
    exact product_projection_two_or_four p A κ
      (fun e => groupM_isMonomial hm (hA e)) hκ 0 1 (by decide)

/-- Only the one literal actual card hypothesis is needed for the support
obstruction. The permutation is explicit and uses no factor coordinates. -/
theorem actual_card_rowSupport_card {m : ℕ} (hm : 0<m) (h : Signature Scalar 6)
    (c : (Bool × Bool) ≃ Fin 4) (γ : Bool)
    (hc : close (n:=4) γ 1 (Tensor.reindex (crossingOrder c).symm h)=0 ∨
      MatchingSample m 2 (close (n:=4) γ 1 (Tensor.reindex (crossingOrder c).symm h))) :
    (rowSupport (contractSource c γ (fun w y => h (pair w.1 w.2 y)))).card=0 ∨
    (rowSupport (contractSource c γ (fun w y => h (pair w.1 w.2 y)))).card=4 := by
  rw [contractSource_eq_actual_close]
  exact matching_packedRows_card hm _ hc

/-- The distinguished-pair projection of a permitted actual card has zero,
two or four words; it can never have the three words forced by P/C. -/
theorem actual_card_projection_card {m : ℕ} (hm : 0<m) (h : Signature Scalar 6)
    (c : (Bool × Bool) ≃ Fin 4) (γ : Bool)
    (hc : close (n:=4) γ 1 (Tensor.reindex (crossingOrder c).symm h)=0 ∨
      MatchingSample m 2 (close (n:=4) γ 1 (Tensor.reindex (crossingOrder c).symm h))) :
    ((rowSupport (contractSource c γ (fun w y => h (pair w.1 w.2 y)))).image Prod.fst).card=0 ∨
    ((rowSupport (contractSource c γ (fun w y => h (pair w.1 w.2 y)))).image Prod.fst).card=2 ∨
    ((rowSupport (contractSource c γ (fun w y => h (pair w.1 w.2 y)))).image Prod.fst).card=4 := by
  rw [contractSource_eq_actual_close]
  exact matching_packedRows_projection hm _ hc

end Holant.Dihedral.SixPortBase.Crossing
