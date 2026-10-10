import Holant.Proofs.Hardness.GeneralEOPairedFamilyMinorRaw

/-! Assignment-by-assignment soundness of the mixed minor compiler, including
heterogeneous row lengths, repeated addresses, zero-arity rows and unused variables. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyMinorValue
open Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GeneralEOPairedCSPFamilyRaw
open scoped BigOperators
namespace W
export GeneralEOPairedFamilyMinorRaw (port row addresses query queryComputes)
end W
namespace Pn
export GeneralEOPairedFamilyExtractionPinRaw (free fixed weight anchor)
end Pn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a b : ℕ → ℕ}
variable (Q : (i : Fin s) → OrientedPerfectPairing (a i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (b i.val))
variable (ports : (i : Fin s) → Fin (P i).count → Bool ⊕ Fin (Q i).count)

private theorem read_block {A B : Type} (xs : List A) (f : A → List B)
    (i : ℕ) (hi : i < xs.length) (j : ℕ) (hj : j < (f xs[i]).length) (d : B) :
    (xs.flatMap f).getD (((xs.take i).flatMap f).length + j) d = (f xs[i]).getD j d := by
  have he : xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
    rw [List.getElem_cons_drop,List.take_append_drop]
  conv_lhs => arg 1; rw [he]
  rw [List.flatMap_append,List.flatMap_cons]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hj]

theorem row_lengths (r : Raw s) :
    (List.finRange r.labels.length).map (fun v => (W.row Q P ports r v).length) =
      r.labels.map (fun i => (P i).count) := by
  apply List.ext_getElem <;> simp [GeneralEOPairedFamilyMinorRaw.row,List.finRange]

theorem prefix_length (r : Raw s) (v : ℕ) :
    (((List.finRange r.labels.length).take v).flatMap (W.row Q P ports r)).length = r.offset P v := by
  rw [List.length_flatMap,List.map_take,row_lengths]
  rfl

theorem addresses_at (r : Raw s) (v : Fin r.labels.length) (j : Fin (P (r.labels.get v)).count) :
    (W.addresses Q P ports r).getD (r.offset P v.val+j.val) 0 =
      W.port Q r v.val (ports (r.labels.get v) j) := by
  have hv : (List.finRange r.labels.length)[v.val]'(by simpa using v.isLt) = v := by
    simp [List.finRange]
  have h := read_block (List.finRange r.labels.length) (W.row Q P ports r)
    v.val (by simpa using v.isLt) j.val
    (by rw [hv]; simpa only [GeneralEOPairedFamilyMinorRaw.row,List.length_ofFn] using j.isLt) 0
  rw [prefix_length,hv] at h
  change (W.addresses Q P ports r).getD _ _ = _ at h
  rw [h]
  change (List.ofFn _).getD j.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa using j.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]

theorem addresses_length (r : Raw s) :
    (W.addresses Q P ports r).length = r.edgeCount P := by
  unfold GeneralEOPairedFamilyMinorRaw.addresses
  rw [List.length_flatMap,row_lengths]
  rfl

theorem query_valid (r : Raw s) (hr : r.WellFormed Q) :
    (Pn.free (W.query Q P ports r)).WellFormed P := by
  constructor
  · exact addresses_length Q P ports r
  · intro k hk
    change k ∈ (List.finRange r.labels.length).flatMap (W.row Q P ports r) at hk
    obtain ⟨v,_,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hk
    change W.port Q r v.val (ports (r.labels.get v) j) < r.variables+2
    cases hq : ports (r.labels.get v) j with
    | inl z => cases z <;> simp [GeneralEOPairedFamilyMinorRaw.port]
    | inr q =>
      change r.addresses.getD (r.offset Q v.val+q.val) 0+2 < r.variables+2
      have hi := GeneralEOPairedFamilyExtractionPinValue.offset_lt Q r v q
      rw [←hr.1] at hi
      have hk := hr.2 _ (List.getElem_mem (h := hi))
      rw [List.getD_eq_getElem _ _ hi]
      omega

variable {K : Type} [CommSemiring K]
variable (g : (i : Fin s) → Signature K (P i).count)

def minor (i : Fin s) : Signature K (Q i).count := fun z =>
  g i (fun j => Sum.elim id z (ports i j))

theorem anchor_port (r : Raw s) (v : ℕ) (x : Fin r.variables → Bool)
    {i : Fin s} (p : Bool ⊕ Fin (Q i).count) :
    Pn.anchor false true x (W.port Q r v p) =
      Sum.elim id (fun j => GeneralEOPairedCSPRaw.read x (r.addresses.getD (r.offset Q v+j.val) 0)) p := by
  cases p with
  | inl b => cases b <;> rfl
  | inr j => rfl

theorem query_value (r : Raw s) :
    Pn.fixed P g (W.query Q P ports r) false true = value Q (minor Q P ports g) r := by
  unfold Pn.fixed value
  apply Finset.sum_congr rfl
  intro x _
  change Fin r.variables → Bool at x
  change (∏ v : Fin r.labels.length, g (r.labels.get v)
    (fun j => Pn.anchor false true x ((W.addresses Q P ports r).getD (r.offset P v.val+j.val) 0))) = _
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext j
  rw [addresses_at]
  exact anchor_port Q r v.val x (ports (r.labels.get v) j)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyMinorValue
