import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinRaw

/-! Exact opposite-reference and distinguishing-row identities. They derive
pin elimination from existing CSP labels, with no unary or disequality oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinValue
open Computability Holant Holant.Tractable Holant.Complexity
open GeneralEOPairedCSPFamilyRaw GeneralEOPairedFamilyExtractionPinRaw
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ} (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable {K : Type*} [Field K]
variable (g : (i : Fin s) → Signature K (P i).count)
variable (label : Fin s) (bits : Fin (P label).count → Bool)

private theorem prefix_get (r : Raw s) (j : Fin (P label).count) :
    ((anchorAddresses P label bits)++r.addresses).getD j.val 0 = if bits j then 1 else 0 := by
  rw [List.getD_append _ _ _ _ (by simp [anchorAddresses])]
  rw [List.getD_eq_getElem _ _ (by simp [anchorAddresses])]
  simp [anchorAddresses]

private theorem tail_get (r : Raw s) (k : ℕ) :
    ((anchorAddresses P label bits)++r.addresses).getD ((P label).count+k) 0=r.addresses.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp [anchorAddresses])]
  simp [anchorAddresses]

theorem augment_weight (r : Raw s) (a : ℕ → Bool) :
    GeneralEOPairedFamilyExtractionPinRaw.weight P g (augment P label bits r) a =
      g label (fun j => a (if bits j then 1 else 0))*GeneralEOPairedFamilyExtractionPinRaw.weight P g r a := by
  change GeneralEOPairedFamilyExtractionWriter.weight P g (label::r.labels)
    (fun k => a ((anchorAddresses P label bits++r.addresses).getD k 0))=_
  rw [GeneralEOPairedFamilyExtractionWriter.weight_cons]
  simp only [prefix_get, tail_get]
  rfl

theorem augment_fixed (r : Raw s) (u v : Bool) :
    fixed P g (augment P label bits r) u v =
      g label (fun j => if bits j then v else u)*fixed P g r u v := by
  change (∑x : Fin r.variables → Bool, GeneralEOPairedFamilyExtractionPinRaw.weight P g (augment P label bits r) (anchor u v x))=_
  simp_rw [augment_weight]
  have hh (x : Fin r.variables → Bool) :
      (fun j => anchor u v x (if bits j then 1 else 0))=(fun j => if bits j then v else u) := by
    funext j
    cases bits j <;> rfl
  simp only [hh, Finset.mul_sum, fixed]

def flip {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun j => !(x j)
def SelfDual : Prop := ∀i x,g i (flip x)=g i x

/-- Every actual occurrence lies inside the serialized address list. -/
theorem offset_lt (r : Raw s) (v : Fin r.labels.length) (j : Fin (P (r.labelsFn v)).count) :
    r.offset P v.val+j.val<r.edgeCount P := by
  have hh := (GeneralEOPairedCSPFamilyCycles.incidence P r.labelsFn v j).isLt
  rw [GeneralEOPairedCSPFamilyCycles.incidence_val, GeneralEOPairedCSPFamilyRaw.count_eq] at hh
  simpa [Raw.labelsFn, Raw.offset, List.map_take] using hh

theorem anchor_flip {n : ℕ} (u v : Bool) (x : Fin n → Bool) (k : ℕ) (hk : k<n+2) :
    anchor (!u) (!v) (flip x) k= !(anchor u v x k) := by
  cases k with
  | zero => rfl
  | succ k => cases k with
    | zero => rfl
    | succ k =>
      have hh : k<n := by omega
      simp [anchor, GeneralEOPairedCSPRaw.read, hh, flip]

theorem weight_flip (hs : SelfDual P g) (r : Raw s) (hr : (free r).WellFormed P)
    (u v : Bool) (x : Fin r.variables → Bool) :
    GeneralEOPairedFamilyExtractionPinRaw.weight P g r (anchor (!u) (!v) (flip x))=GeneralEOPairedFamilyExtractionPinRaw.weight P g r (anchor u v x) := by
  unfold GeneralEOPairedFamilyExtractionPinRaw.weight GeneralEOPairedFamilyExtractionWriter.weight
  apply Finset.prod_congr rfl
  intro row _
  have he : (fun j : Fin (P (r.labels.get row)).count => anchor (!u) (!v) (flip x)
      (r.addresses.getD (r.offset P row.val+j.val) 0))=
      flip (fun j => anchor u v x (r.addresses.getD (r.offset P row.val+j.val) 0)) := by
    funext j
    apply anchor_flip
    apply hr.2
    have hj : r.offset P row.val+j.val<r.addresses.length := by
      have hl : r.addresses.length=r.edgeCount P := hr.1
      rw [hl]
      exact offset_lt P r row j
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  change g (r.labels.get row) (fun j => anchor (!u) (!v) (flip x)
      (r.addresses.getD (r.offset P row.val+j.val) 0))=_
  exact (congrArg (g (r.labels.get row)) he).trans (hs _ _)

theorem fixed_flip (hs : SelfDual P g) (r : Raw s) (hr : (free r).WellFormed P)
    (u v : Bool) : fixed P g r (!u) (!v)=fixed P g r u v := by
  let e : (Fin r.variables → Bool) ≃ (Fin r.variables → Bool) :=
    { toFun := flip, invFun := flip,
      left_inv := by intro x; funext j; exact Bool.not_not _,
      right_inv := by intro x; funext j; exact Bool.not_not _ }
  unfold fixed
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  exact weight_flip P g hs r hr u v x

section Field

/-- The two raw queries subtract exactly the same-anchor assignments. -/
theorem opposite (r : Raw s) :
    value P g (free r)-value P g (merge r)=fixed P g r false true+fixed P g r true false := by
  rw [free_value, merge_value]
  ring

/-- The distinguishing row supplies the second equation using two further
literal mixed-family records. -/
theorem weighted_opposite (r : Raw s) :
    value P g (free (augment P label bits r))-value P g (merge (augment P label bits r))=
      g label bits*fixed P g r false true+g label (flip bits)*fixed P g r true false := by
  rw [opposite, augment_fixed, augment_fixed]
  have h0 : (fun j => if bits j then true else false)=bits := by funext j; cases bits j <;> rfl
  have h1 : (fun j => if bits j then false else true)=flip bits := by funext j; simp only [flip]; cases bits j <;> rfl
  rw [h0,h1]

/-- Four evaluations recover the oriented 01 pins. The denominator is an
internally selectable literal difference of complementary row coefficients. -/
theorem recover_distinguished (hne : g label bits≠g label (flip bits)) (r : Raw s) :
    fixed P g r false true =
      ((value P g (free (augment P label bits r))-value P g (merge (augment P label bits r)))-
        g label (flip bits)*(value P g (free r)-value P g (merge r)))/
          (g label bits-g label (flip bits)) := by
  rw [weighted_opposite, opposite]
  apply (eq_div_iff (sub_ne_zero.mpr hne)).mpr
  ring

/-- In the invariant case two evaluations suffice, even with unused
references: global complementation pairs the opposite-anchor assignments. -/
theorem recover_selfdual [CharZero K] (hs : SelfDual P g) (r : Raw s)
    (hr : (free r).WellFormed P) :
    fixed P g r false true=(value P g (free r)-value P g (merge r))/2 := by
  rw [opposite]
  have h := fixed_flip P g hs r hr false true
  change fixed P g r true false=fixed P g r false true at h
  rw [h]
  apply (eq_div_iff (by norm_num : (2:K)≠0)).mpr
  ring

end Field
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPinValue
