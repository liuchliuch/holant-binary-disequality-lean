import Holant.Proofs.Tractability.EOEvaluation.PairingConstruction
import Holant.Proofs.Tractability.LocalAffineMachine.Relabel.LocalWords


namespace Holant.LocalDrafts.Tractability.EOEvaluation.PairingTemplates
open Turing Computability Holant Holant.Tractable Holant.Complexity
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
open BinaryCompose FixedFieldMachines GraphPreprocessing PairingCharacters Distribution
open scoped BigOperators
noncomputable section

abbrev Template (n : ℕ) := (Fin (n / 2) × Bool) ≃ Fin n
abbrev Mask (n : ℕ) := Word (Fintype.card (Word n))
def entry {n : ℕ} (m : Mask n) (x : Word n) : Bool := m (Fintype.equivFin (Word n) x)
def points {n : ℕ} (m : Mask n) : Finset (Word n) := Finset.univ.filter (fun x => entry m x = true)
def Good {n : ℕ} (m : Mask n) : Prop :=
  (∀ x, entry m x = true → Holant.charge x = 0) ∧
  (∀ a b c, entry m a = true → entry m b = true → entry m c = true → entry m (tripleXor a b c) = true)
def Covers {n : ℕ} (m : Mask n) (p : Template n) : Prop :=
  ∀ x, entry m x = true → ∀ j, x (p (j, false)) ≠ x (p (j, true))

instance coversDecidable {n : ℕ} (m : Mask n) (p : Template n) : Decidable (Covers m p) := by
  unfold Covers
  infer_instance

def normalize {n : ℕ} (D : Data n) : Template n :=
  (Equiv.prodCongr (finCongr (by have h := PairingConstruction.twice_count D; omega))
    (Equiv.refl Bool)).trans (PairingConstruction.pairing D).ports

theorem normalize_covers {n : ℕ} (D : Data n) (x : Word n) (hx : x ∈ D.points) (j : Fin (n / 2)) :
    x (normalize D (j, false)) ≠ x (normalize D (j, true)) :=
  PairingConstruction.covers D x hx _

def emptyTemplate {n : ℕ} (hn : ∃ d, n = 2 * d) : Template n :=
  Fintype.equivOfCardEq (by obtain ⟨d, rfl⟩ := hn; simp [Fintype.card_prod, Nat.mul_comm])

theorem exists_cover {n : ℕ} (hn : ∃ d, n = 2 * d) (m : Mask n) (hm : Good m) :
    ∃ p : Template n, Covers m p := by
  classical
  by_cases hs : (points m).Nonempty
  · obtain ⟨a, ha⟩ := hs
    let D : Data n := {
      points := points m
      base := ⟨a, ha⟩
      central := fun x hx => hm.1 x (by simpa [points] using hx)
      closed := by
        intro x hx y hy z hz
        simpa [points] using hm.2 x y z (by simpa [points] using hx)
          (by simpa [points] using hy) (by simpa [points] using hz) }
    refine ⟨normalize D, ?_⟩
    intro x hx j
    exact normalize_covers D x (by simpa [D, points] using hx) j
  · refine ⟨emptyTemplate hn, ?_⟩
    intro x hx j
    exact False.elim (hs ⟨x, by simp [points, hx]⟩)

abbrev Label (n : ℕ) := Fin (Fintype.card (Template n))
def decode {n : ℕ} (i : Label n) : Template n := (Fintype.equivFin (Template n)).symm i

def search {n : ℕ} (m : Mask n) : List (Label n) → Option (Label n)
  | [] => none
  | i :: is => if Covers m (decode i) then some i else search m is

theorem search_sound {n : ℕ} (m : Mask n) (is : List (Label n)) (i : Label n)
    (h : search m is = some i) : Covers m (decode i) := by
  classical
  induction is with
  | nil => simp [search] at h
  | cons j is ih =>
    by_cases hj : Covers m (decode j)
    · simp only [search, if_pos hj] at h
      have he : j = i := Option.some.inj h
      exact he ▸ hj
    · apply ih; simpa [search, hj] using h

theorem search_none {n : ℕ} (m : Mask n) (is : List (Label n)) :
    search m is = none ↔ ∀ i ∈ is, ¬ Covers m (decode i) := by
  classical
  induction is with
  | nil => simp [search]
  | cons i is ih => by_cases hi : Covers m (decode i) <;> simp [search, hi, ih]

def select {n : ℕ} (m : Mask n) : Option (Label n) := search m (List.finRange _)

theorem select_complete {n : ℕ} (hn : ∃ d, n = 2 * d) (m : Mask n) (hm : Good m) :
    ∃ i, select m = some i ∧ Covers m (decode i) := by
  classical
  obtain ⟨p, hp⟩ := exists_cover hn m hm
  cases h : select m with
  | none =>
    have hh := (search_none m (List.finRange _)).mp h
    exact False.elim (hh (Fintype.equivFin (Template n) p) (by simp) (by simpa [decode] using hp))
  | some i => exact ⟨i, rfl, search_sound m _ i h⟩

def inputEncoding (n : ℕ) := LocalAffineMachine.Relabel.LocalWords.fixedEncoding (Fintype.card (Word n))
def outputEncoding (n : ℕ) := optionEncoding (SignatureLabel.binaryFinEncoding (Fintype.card (Template n)))

def computes (n : ℕ) : Computes (inputEncoding n) (outputEncoding n) (select (n := n)) :=
  FiniteRecode.computes (inputEncoding n) (outputEncoding n) select
    (4 * Fintype.card (Word n) + 1)
    (fun m => le_of_eq (LocalAffineMachine.Relabel.LocalWords.fixed_length _ m))

theorem primitive_bound (n : ℕ) (m : Mask n) :
    primitiveCost (computes n).machine ((computes n).outputs m).steps
      (some (Turing.initList (computes n).machine.computer ((inputEncoding n).encode m))) ≤
        (primitivePolynomial (computes n)).eval ((inputEncoding n).encode m).length :=
  computes_primitive_cost (computes n) m

end
end Holant.LocalDrafts.Tractability.EOEvaluation.PairingTemplates
