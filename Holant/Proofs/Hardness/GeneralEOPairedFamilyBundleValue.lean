import Holant.Proofs.Hardness.GeneralEOPairedFamilyBundleRaw
import Holant.Proofs.Hardness.GeneralEOPairedFamilyMinorValue

/-! Exact finite-factor expansion, proved by individual assignments. Empty
recipes contribute one; repeated parent factors and nullary rows are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue
open Holant Holant.Tractable GeneralEOPairedCSPFamilyRaw
open scoped BigOperators
namespace W
export GeneralEOPairedFamilyBundleRaw (Node Recipe factor rowFor row data query)
end W
namespace M
export GeneralEOPairedFamilyMinorRaw (port)
export GeneralEOPairedFamilyMinorValue (anchor_port)
end M
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (free fixed weight anchor)
end Pn
namespace T
export GeneralEOPairedFamilyExtractionWriter (weight weight_cons weight_nil)
end T
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s t : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (j : Fin t) → OrientedPerfectPairing (b j.val))
variable (recipe : W.Recipe Q P)

theorem data_length (r : Raw s) :
    ∀ c ∈ W.data Q P recipe r, c.2.length = (P c.1).count := by
  intro c hc
  obtain ⟨v,_,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨node,_,rfl⟩ := List.mem_map.mp hc
  simp [GeneralEOPairedFamilyBundleRaw.factor]

theorem query_valid (r : Raw s) (hr : r.WellFormed Q) :
    (Pn.free (W.query Q P recipe r)).WellFormed P := by
  constructor
  · change ((W.data Q P recipe r).flatMap Prod.snd).length =
      (((W.data Q P recipe r).map Prod.fst).map (fun i => (P i).count)).sum
    rw [List.length_flatMap,List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact data_length Q P recipe r c hc
  · intro k hk
    change k ∈ (W.data Q P recipe r).flatMap Prod.snd at hk
    obtain ⟨c,hc,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨v,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨node,_,rfl⟩ := List.mem_map.mp hc
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hk
    change M.port Q r v.val (node.2 j) < r.variables+2
    cases hq : node.2 j with
    | inl z => cases z <;> simp [GeneralEOPairedFamilyMinorRaw.port]
    | inr q =>
      change r.addresses.getD (r.offset Q v.val+q.val) 0+2 < r.variables+2
      have hi := GeneralEOPairedFamilyExtractionPinValue.offset_lt Q r v q
      rw [←hr.1] at hi
      have hk := hr.2 _ (List.getElem_mem (h := hi))
      rw [List.getD_eq_getElem _ _ hi]
      omega

variable {K : Type} [CommSemiring K]
variable (g : (j : Fin t) → Signature K (P j).count)

def coefficient (i : Fin s) : Signature K (Q i).count := fun z =>
  ((recipe i).map fun node => g node.1 (fun j => Sum.elim id z (node.2 j))).prod

private theorem weight_data (cs : List (Fin t × List ℕ))
    (hc : ∀ c ∈ cs, c.2.length = (P c.1).count) (z : ℕ → Bool) :
    T.weight P g (cs.map Prod.fst) (fun k => z ((cs.flatMap Prod.snd).getD k 0)) =
      (cs.map fun c => g c.1 (fun j => z (c.2.getD j.val 0))).prod := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rcases c with ⟨i,ps⟩
    have hp : ps.length = (P i).count := hc (i,ps) (by simp)
    have hs : ∀ c ∈ cs, c.2.length = (P c.1).count := fun c hm => hc c (by simp [hm])
    simp only [List.map_cons,List.flatMap_cons,List.prod_cons,T.weight_cons]
    apply congrArg₂ (· * ·)
    · congr 1
      funext j
      rw [List.getD_append _ _ _ _ (by omega)]
    · have he : (fun k => z ((ps ++ cs.flatMap Prod.snd).getD ((P i).count+k) 0)) =
          (fun k => z ((cs.flatMap Prod.snd).getD k 0)) := by
        funext k
        rw [←hp,List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
      rw [he]
      exact ih hs

private theorem product_flatMap {A : Type} (xs : List A) (f : A → List K) :
    (xs.flatMap f).prod = (xs.map fun a => (f a).prod).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_cons,List.prod_cons,List.prod_append,ih]

theorem query_value (r : Raw s) :
    Pn.fixed P g (W.query Q P recipe r) false true = value Q (coefficient Q P recipe g) r := by
  unfold Pn.fixed value
  apply Finset.sum_congr rfl
  intro x _
  change Fin r.variables → Bool at x
  change T.weight P g ((W.data Q P recipe r).map Prod.fst)
    (fun k => Pn.anchor false true x (((W.data Q P recipe r).flatMap Prod.snd).getD k 0)) = _
  rw [weight_data P g _ (data_length Q P recipe r)]
  unfold GeneralEOPairedFamilyBundleRaw.data GeneralEOPairedFamilyBundleRaw.row
    GeneralEOPairedFamilyBundleRaw.rowFor
  rw [List.map_flatMap,product_flatMap,←List.ofFn_eq_map,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  unfold coefficient
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro node _
  dsimp only [Function.comp_def,GeneralEOPairedFamilyBundleRaw.factor]
  congr 1
  funext j
  rw [List.getD_eq_getElem _ _ (by simpa using j.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]
  exact M.anchor_port Q r v.val x (node.2 j)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue
