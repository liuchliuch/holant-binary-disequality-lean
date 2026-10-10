import Holant.Pauli.ExoticKlein.SixPortIntegerCertificate

/-! Sparse integer row certificates with kernel-checked normalization. The
soundness theorem reduces every accepted sparse identity to the existing
Gaussian-integer checker. Coordinates outside the finite tensor domain are
harmless; no support bound or external arithmetic oracle is trusted. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SparseInteger
open Holant.Pauli.ExoticKlein.SixPort
open IntegerCertificate (IRow mapRows)
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

abbrev Row := List (ℕ × ℤ)

def value : Row → ℕ → ℤ
  | [],_ => 0
  | (j,c)::r,i => (if i=j then c else 0) + value r i

def insert (j : ℕ) (c : ℤ) : Row → Row
  | [] => if c=0 then [] else [(j,c)]
  | (k,d)::r => if j<k then (if c=0 then (k,d)::r else (j,c)::(k,d)::r)
    else if j=k then (if c+d=0 then r else (k,c+d)::r)
    else (k,d)::insert j c r

theorem insert_value (j : ℕ) (c : ℤ) (r : Row) (i : ℕ) :
    value (insert j c r) i = (if i=j then c else 0) + value r i := by
  induction r with
  | nil => by_cases h : c=0 <;> simp [insert,value,h]
  | cons p r ih =>
      obtain ⟨k,d⟩ := p
      simp only [insert]
      split_ifs <;> by_cases hi : i=j <;> by_cases hk : i=k <;>
        simp_all [value] <;> omega

def normalize : Row → Row
  | [] => []
  | (j,c)::r => insert j c (normalize r)

theorem normalize_value (r : Row) (i : ℕ) : value (normalize r) i = value r i := by
  induction r with
  | nil => rfl
  | cons p r ih => obtain ⟨j,c⟩ := p; simp only [normalize,insert_value,value,ih]

def scale (c : ℤ) (r : Row) : Row := r.map (fun p => (p.1,c*p.2))

theorem value_append (a b : Row) (i : ℕ) : value (a++b) i = value a i + value b i := by
  induction a with
  | nil => simp [value]
  | cons p a ih => obtain ⟨j,c⟩ := p; simp [value,ih,add_assoc]

theorem value_scale (c : ℤ) (r : Row) (i : ℕ) : value (scale c r) i = c * value r i := by
  induction r with
  | nil => simp [scale,value]
  | cons p r ih =>
      obtain ⟨j,d⟩ := p
      simp only [scale,List.map_cons,value] at *
      by_cases h : i=j <;> simp_all [mul_add]

def combine (rows : List Row) : List (ℕ × ℤ) → Row
  | [] => []
  | (j,c)::w => scale c (rows.getD j []) ++ combine rows w

structure Witness where
  denominator : ℕ
  weights : List (ℕ × ℤ)

def checkRow (rows : List Row) (row : Row) (w : Witness) : Bool :=
  decide (0<w.denominator) && decide
    (normalize (scale w.denominator row) = normalize (combine rows w.weights))

def toIRow {n : ℕ} (r : Row) : IRow n :=
  fun i => (value r i.val : GZ)

def toIRows {n : ℕ} (rows : List Row) : List (IRow n) := rows.map toIRow

def Witness.toInteger (w : Witness) : IntegerCertificate.Witness where
  denominator := w.denominator
  weights := w.weights.map (fun p => (p.1,(p.2 : GZ)))

theorem toIRow_append {n : ℕ} (a b : Row) :
    (toIRow (a++b) : IRow n) = toIRow a + toIRow b := by
  funext i
  simp [toIRow,value_append]

theorem toIRow_scale {n : ℕ} (c : ℤ) (r : Row) :
    (toIRow (scale c r) : IRow n) = fun i => (c : GZ)*toIRow r i := by
  funext i
  simp [toIRow,value_scale]

theorem toIRows_getD {n : ℕ} (rows : List Row) (j : ℕ) :
    (toIRows rows).getD j (fun _ : Fin n => 0) = toIRow (rows.getD j []) := by
  induction rows generalizing j with
  | nil => cases j <;> rfl
  | cons r rows ih => cases j with
    | zero => rfl
    | succ j => exact ih j

theorem toIRow_combine {n : ℕ} (rows : List Row) (w : List (ℕ × ℤ)) :
    (toIRow (combine rows w) : IRow n) =
      IntegerCertificate.combine (toIRows rows) (w.map (fun p => (p.1,(p.2 : GZ)))) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
      obtain ⟨j,c⟩ := p
      rw [combine,toIRow_append,toIRow_scale,ih]
      funext i
      simp only [List.map_cons,IntegerCertificate.combine,Pi.add_apply,toIRows_getD]

theorem checked_row_to_integer {n : ℕ} (rows : List Row) (row : Row) (w : Witness)
    (checked : checkRow rows row w = true) :
    IntegerCertificate.checkRow (toIRows rows) (toIRow row : IRow n) w.toInteger = true := by
  obtain ⟨positive,equation⟩ := Bool.and_eq_true_iff.mp checked
  have hd : 0<w.denominator := of_decide_eq_true positive
  have he : normalize (scale w.denominator row) = normalize (combine rows w.weights) := of_decide_eq_true equation
  have hrow : (toIRow (scale w.denominator row) : IRow n) = toIRow (combine rows w.weights) := by
    funext i
    have hv := congrArg (fun r => value r i.val) he
    rw [normalize_value,normalize_value] at hv
    exact congrArg (fun z : ℤ => (z : GZ)) hv
  rw [toIRow_scale,toIRow_combine] at hrow
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hd,?_⟩
  apply decide_eq_true
  simpa only [Witness.toInteger,Int.cast_natCast] using hrow

structure Reduction where
  rows : List Row
  witnesses : Fin rows.length → Witness

def Reduction.check (r : Reduction) (rows : List Row) : Bool :=
  decide (∀ i : Fin r.rows.length, checkRow rows (r.rows.get i) (r.witnesses i) = true)

theorem Reduction.sound {n : ℕ} (r : Reduction) (rows : List Row)
    (checked : r.check rows = true) {s : Fin n → ℂ}
    (satisfies : LinearCertificate.Satisfies (mapRows (toIRows rows)) s) :
    LinearCertificate.Satisfies (mapRows (toIRows r.rows)) s := by
  have hc : ∀ i : Fin r.rows.length, checkRow rows (r.rows.get i) (r.witnesses i) = true := of_decide_eq_true checked
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hb
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc'
  exact IntegerCertificate.checked_row_sound (checked_row_to_integer rows _ _ (hc i)) satisfies

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SparseInteger
