import Holant.Certificates.NormalizedDihedralQ6.Data

/-! The exact printed 6-by-8 certificate in Proposition A.9. Every finite assertion
is proved by kernel reduction (`decide`), never native evaluation or an imported
external verifier verdict. -/
namespace Holant.Certificates.NormalizedDihedralQ6
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000
abbrev Witness := Pair × Bool × ℕ

def bitIndex (a b o : Bool) : Fin 8 :=
  if a then if b then if o then 7 else 6 else if o then 5 else 4
  else if b then if o then 3 else 2 else if o then 1 else 0

def printedTable : Fin 6 → Fin 8 → Option Witness :=
  ![![some ((0,4),false,8),some ((1,4),false,8),none,none,
       some ((0,4),false,8),some ((1,4),false,8),some ((0,4),false,8),some ((0,5),false,8)],
    ![some ((0,5),false,8),some ((1,5),false,8),some ((1,3),true,6),some ((0,3),true,6),
       some ((0,3),false,6),some ((1,3),false,6),some ((1,5),false,8),some ((0,5),false,8)],
    ![some ((0,4),false,8),some ((1,4),false,8),some ((1,3),true,6),some ((0,3),true,6),
       some ((0,3),false,6),some ((1,3),false,6),some ((1,4),false,8),some ((0,4),false,8)],
    ![some ((0,5),false,8),some ((1,5),false,8),some ((1,2),true,6),some ((0,2),true,6),
       some ((0,2),false,6),some ((1,2),false,6),some ((1,5),false,8),some ((0,5),false,8)],
    ![some ((0,4),false,8),some ((1,4),false,8),some ((1,2),true,6),some ((0,2),true,6),
       some ((0,2),false,6),some ((1,2),false,6),some ((1,4),false,8),some ((0,4),false,8)],
    ![some ((0,2),false,6),some ((0,2),true,6),some ((0,4),false,6),some ((0,4),false,6),
       some ((0,2),false,6),some ((0,2),true,6),some ((0,2),false,6),some ((0,2),true,6)]]

def printedWitness (d : Sector) : Option Witness := printedTable d.1 (bitIndex d.2.1 d.2.2.1 d.2.2.2)
def matchingCase (d : Sector) : Bool := d.1 == 0 && !d.2.1 && d.2.2.1

def isolatedPort (d : Sector) : Port :=
  if d.1 = 0 then if d.2.1 then 2 else if d.2.2.2 then 0 else 1
  else if d.1 = 5 then 0 else 2

theorem canonical_card : ∀ d : Sector, (canonicalSupport d).card = 8 := by decide

theorem printed_none_iff : ∀ d : Sector, (printedWitness d = none) ↔ matchingCase d = true := by decide

def EntryCorrect (d : Sector) (w : Option Witness) : Prop :=
  match w with
  | none => True
  | some (p,γ,n) => p.1 < p.2 ∧ (n = 6 ∨ n = 8) ∧
      (slice (canonicalSupport d) p γ).card = n ∧ (projected (canonicalSupport d) p γ).card = n
instance entryDecidable (d : Sector) (w : Option Witness) : Decidable (EntryCorrect d w) := by
  cases w with
  | none => exact inferInstanceAs (Decidable True)
  | some w => rcases w with ⟨p,γ,n⟩; exact inferInstanceAs (Decidable
      (p.1 < p.2 ∧ (n = 6 ∨ n = 8) ∧ (slice (canonicalSupport d) p γ).card = n ∧
        (projected (canonicalSupport d) p γ).card = n))

def EntryMaximal (d : Sector) (w : Option Witness) : Prop :=
  match w with
  | none => True
  | some (_,_,n) => ∀ p ∈ pairs, ∀ γ : Bool,
      (projected (canonicalSupport d) p γ).card = (slice (canonicalSupport d) p γ).card →
      (slice (canonicalSupport d) p γ).card ≤ n
instance maximalDecidable (d : Sector) (w : Option Witness) : Decidable (EntryMaximal d w) := by
  cases w with
  | none => exact inferInstanceAs (Decidable True)
  | some w => rcases w with ⟨p,γ,n⟩; exact inferInstanceAs (Decidable
      (∀ p ∈ pairs, ∀ γ : Bool,
        (projected (canonicalSupport d) p γ).card = (slice (canonicalSupport d) p γ).card →
        (slice (canonicalSupport d) p γ).card ≤ n))

/-- Every printed ij_gamma^s entry has exactly s retained words and s distinct images. -/
theorem printed_entries_checked : ∀ d : Sector, EntryCorrect d (printedWitness d) := by decide

/-- Exhaustive maximality over15 pairs, both parity slices, all48 canonical cases. -/
theorem printed_maximality_checked : ∀ d : Sector, EntryMaximal d (printedWitness d) := by decide

/-- A semantic nonmatching obstruction: one port has no constant-XOR partner. -/
theorem isolated_checked : ∀ d : Sector, matchingCase d = false → ∀ j : Port, j ≠ isolatedPort d →
    ∃ x ∈ canonicalSupport d, ∃ y ∈ canonicalSupport d,
      parity (isolatedPort d,j) x ≠ parity (isolatedPort d,j) y := by decide

theorem canonical_counts :
    ((Finset.univ : Finset Sector).filter (fun d => printedWitness d = none)).card = 2 ∧
    ((Finset.univ : Finset Sector).filter (fun d => ∃ p γ, printedWitness d = some (p,γ,6))).card = 24 ∧
    ((Finset.univ : Finset Sector).filter (fun d => ∃ p γ, printedWitness d = some (p,γ,8))).card = 22 := by decide

end Holant.Certificates.NormalizedDihedralQ6
