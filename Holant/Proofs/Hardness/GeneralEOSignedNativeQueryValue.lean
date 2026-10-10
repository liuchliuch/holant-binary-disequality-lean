import Holant.Proofs.Hardness.GeneralEOSignedNativeQuery

/-! The emitted signed CSP table has exactly the weighted sum of the decoded
native graph's component-normalized rows. All heterogeneous row offsets and
nullary occurrences are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeQueryValue
open Holant Holant.Tractable Holant.Complexity
open scoped BigOperators
namespace Q
export GeneralEOSignedNativeQuery (count label signs rowLabel rowScopes query count_row)
end Q
namespace R
export GeneralEOSignedNativeRaw (Input rowPairing)
end R
namespace D
export GeneralEOSignedNativeDecoded (label pairing signedQueryValue)
end D
namespace N
export GeneralEOSignedNativeParity (signedScope signedInput)
end N
namespace S
export GeneralEOPairedFamilySigned (pairing value signed_compressed)
end S
namespace F
export GeneralEOPairedCSPFamilyRaw (Raw value)
end F
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))

private theorem read_block {A B : Type} (xs : List A) (f : A → List B)
    (i : ℕ) (hi : i < xs.length) (j : ℕ) (hj : j < (f xs[i]).length) (d : B) :
    (xs.flatMap f).getD (((xs.take i).flatMap f).length + j) d = (f xs[i]).getD j d := by
  have he : xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
    rw [List.getElem_cons_drop,List.take_append_drop]
  conv_lhs => arg 1; rw [he]
  rw [List.flatMap_append,List.flatMap_cons]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  rw [Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hj]

theorem row_lengths (r : R.Input (s:=s) (arity:=arity)) :
    (List.finRange r.val.vertices.length).map (fun v => (Q.rowScopes P r v).length) =
      (Q.query P r).labels.map (fun i => (S.pairing P (Q.label P) (Q.signs P) i).count) := by
  simp [Q.query,Q.rowScopes,List.finRange,List.map_ofFn,Function.comp_def,R.rowPairing,D.label]

theorem prefix_length (r : R.Input (s:=s) (arity:=arity)) (v : ℕ) :
    (((List.finRange r.val.vertices.length).take v).flatMap (Q.rowScopes P r)).length =
      (Q.query P r).offset (S.pairing P (Q.label P) (Q.signs P)) v := by
  rw [List.length_flatMap,List.map_take,row_lengths]
  rfl

theorem addresses_at (r : R.Input (s:=s) (arity:=arity)) (v : Fin r.val.vertices.length)
    (j : Fin (P (D.label r v)).count) :
    (Q.query P r).addresses.getD
      ((Q.query P r).offset (S.pairing P (Q.label P) (Q.signs P)) v.val+j.val) 0 =
      (N.signedScope (r.val.shape r.property) (R.rowPairing P r) v j).1.val := by
  have hv : (List.finRange r.val.vertices.length)[v.val]'(by simpa using v.isLt) = v := by
    simp [List.finRange]
  have h := read_block (List.finRange r.val.vertices.length) (Q.rowScopes P r)
    v.val (by simpa using v.isLt) j.val
    (by rw [hv]; simpa only [Q.rowScopes,List.length_ofFn,R.rowPairing,D.label] using j.isLt) 0
  rw [prefix_length,hv] at h
  change (Q.query P r).addresses.getD _ _ = _ at h
  rw [h]
  change (List.ofFn _).getD j.val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn,R.rowPairing,D.label] using j.isLt)]
  simp only [List.getElem_ofFn,Fin.eta]

theorem query_valid (r : R.Input (s:=s) (arity:=arity)) :
    (Q.query P r).WellFormed (S.pairing P (Q.label P) (Q.signs P)) := by
  constructor
  · change ((List.finRange r.val.vertices.length).flatMap (Q.rowScopes P r)).length = _
    rw [List.length_flatMap,row_lengths]
    rfl
  · intro a ha
    change a ∈ (List.finRange r.val.vertices.length).flatMap (Q.rowScopes P r) at ha
    obtain ⟨v,_,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact (N.signedScope (r.val.shape r.property) (R.rowPairing P r) v j).1.isLt

variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable (G : (i : Fin s) → Signature K (arity i.val))

private def rowEval (q : GeneralEOSignedNativeQuery.Palette P) (a : ℕ → Bool) : K :=
  GeneralEOPairedCSPCycles.compress (P q.1) (G q.1) (fun j => Bool.xor (q.2 j) (a j.val))

theorem query_value (r : R.Input (s:=s) (arity:=arity)) :
    S.value G P (Q.label P) (Q.signs P) (Q.query P r) = D.signedQueryValue G P r := by
  rw [S.value,GeneralEOPairedCSPFamilyNative.totalValue,ite_eq_left (query_valid P r)]
  unfold F.value D.signedQueryValue
  apply Finset.sum_congr rfl
  intro x _
  change Fin (r.val.edges.length*2) → Bool at x
  symm
  apply Fintype.prod_equiv (finCongr (GeneralEOSignedNativeQuery.rows_preserved P r)).symm
  intro v
  symm
  have hl : (Q.query P r).labelsFn
      ((finCongr (GeneralEOSignedNativeQuery.rows_preserved P r)).symm v) = Q.rowLabel P r v := by
    simp [GeneralEOPairedCSPFamilyRaw.Raw.labelsFn,Q.query,finCongr]
  rw [hl]
  dsimp only
  rw [S.signed_compressed]
  let readRow : ℕ → Bool := fun k => GeneralEOPairedCSPRaw.read x
    ((Q.query P r).addresses.getD
      ((Q.query P r).offset (S.pairing P (Q.label P) (Q.signs P)) v.val+k) 0)
  change rowEval P G ((GeneralEOSignedNativeQuery.enumeration P).symm (Q.rowLabel P r v)) readRow = _
  rw [GeneralEOSignedNativeQuery.rowLabel,(GeneralEOSignedNativeQuery.enumeration P).symm_apply_apply]
  change GeneralEOPairedCSPCycles.compress (P (D.label r v)) (G (D.label r v))
    (fun j => Bool.xor (GeneralEOSignedNativeQuery.rowSigns P r v j) (readRow j.val)) = _
  apply congrArg (GeneralEOPairedCSPCycles.compress (P (D.label r v)) (G (D.label r v)))
  funext j
  change Bool.xor (GeneralEOSignedNativeQuery.rowSigns P r v j)
    (GeneralEOPairedCSPRaw.read x ((Q.query P r).addresses.getD
      ((Q.query P r).offset (S.pairing P (Q.label P) (Q.signs P)) v.val+j.val) 0)) = _
  rw [addresses_at,GeneralEOPairedCSPRaw.read_at]
  rfl

theorem value_eq (G : (i : Fin s) → Signature K (arity i.val))
    (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
    (r : R.Input (s:=s) (arity:=arity)) :
    S.value G P (Q.label P) (Q.signs P) (Q.query P r) = D.signedQueryValue G P r :=
  query_value P G r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeQueryValue
