import Holant.Certificates.NormalizedDihedralQ6.SourceParameters
import Holant.Certificates.NormalizedDihedralQ6.Source
import Holant.Certificates.NormalizedDihedralQ6.CubeAction

/-! Literal main-text four-flat data. The port permutation records the original
ordered distinguished pair; each sector keeps its own fixed edge and ordered
varying edge. Coefficients are not normalized or identified. -/
namespace Holant.Dihedral.SixToFour
open Holant.Certificates.NormalizedDihedralQ6
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

/-- The source chooses a residual matching, one fixed edge, three bits, and an
orientation of the varying edge. -/
abbrev SectorData := SourceSector × Bool

def sector (d : SectorData) : Sector :=
  let e := sourceSectorEquiv d.1
  (e.1,e.2.1,e.2.2.1,if d.2 then e.2.2.2 ^^ e.2.2.1 else e.2.2.2)

def fixed (d : SectorData) : Pair := fixedEdge (sector d).1

def varying (d : SectorData) : Pair :=
  let p := varyingEdge (sector d).1
  if d.2 then (p.2,p.1) else p

/-- Exactly the three displayed equations in eq:app-nd-four-flat-support,
with z equal to the first distinguished bit. -/
def sectorEquations (ε : Bool) (d : SectorData) (x : Word) : Prop :=
  x 1 = (x 0 ^^ ε) ∧
  (x (fixed d).1 ^^ x (fixed d).2) = d.1.2.2.1 ∧
  x (varying d).1 = (d.1.2.2.2.2 ^^ x 0) ∧
  x (varying d).2 = (d.1.2.2.2.2 ^^ x 0 ^^ d.1.2.2.2.1)

instance (ε : Bool) (d : SectorData) (x : Word) : Decidable (sectorEquations ε d x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

private def canonicalEquations (ε : Bool) (d : Sector) (x : Word) : Prop :=
  x 1 = (x 0 ^^ ε) ∧
  x (fixedEdge d.1).2 = (x (fixedEdge d.1).1 ^^ d.2.1) ∧
  x (varyingEdge d.1).1 = (d.2.2.2 ^^ x 0) ∧
  x (varyingEdge d.1).2 = (d.2.2.2 ^^ x 0 ^^ d.2.2.1)

private theorem mem_sector_iff (ε : Bool) (d : Sector) (x : Word) :
    x ∈ (sectorWords ε d).toFinset ↔ ∃ z w, x = sectorWord ε d z w := by
  simp only [sectorWords,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨false,false,rfl⟩
    · exact ⟨false,true,rfl⟩
    · exact ⟨true,false,rfl⟩
    · exact ⟨true,true,rfl⟩
  · rintro ⟨z,w,rfl⟩
    cases z <;> cases w <;> simp

private theorem canonical_equations_iff (ε : Bool) (d : Sector) (x : Word) :
    x ∈ (sectorWords ε d).toFinset ↔ canonicalEquations ε d x := by
  rw [mem_sector_iff]
  constructor
  · rintro ⟨z,w,rfl⟩
    obtain ⟨h0,h1,he0,he1,hf0,hf1⟩ := sector_equations ε d z w
    exact ⟨h1.trans (congrArg (· ^^ ε) h0.symm),
      he1.trans (congrArg (· ^^ d.2.1) he0.symm),
      hf0.trans (congrArg (d.2.2.2 ^^ ·) h0.symm),
      hf1.trans (congrArg (fun b => d.2.2.2 ^^ b ^^ d.2.2.1) h0.symm)⟩
  · rintro ⟨h1,he1,hf0,hf1⟩
    refine ⟨x 0,x (fixedEdge d.1).1,?_⟩
    funext i
    by_cases h0 : i = 0
    · subst i; simp [sectorWord]
    by_cases hi1 : i = 1
    · subst i; simpa [sectorWord] using h1
    have hr : 2 ≤ i.val := by
      have hz : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have ho : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
      omega
    have hh := (residual_edges d.1).2.2.2 i
    have hi := hh.mpr hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    obtain ⟨he,hf,hn,_⟩ := residual_edges d.1
    have hne : (fixedEdge d.1).1 ≠ (fixedEdge d.1).2 := ne_of_lt he
    have hcross : (varyingEdge d.1).1 ≠ (fixedEdge d.1).1 ∧
        (varyingEdge d.1).1 ≠ (fixedEdge d.1).2 ∧
        (varyingEdge d.1).2 ≠ (fixedEdge d.1).1 ∧
        (varyingEdge d.1).2 ≠ (fixedEdge d.1).2 := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,and_true] at hn
      exact ⟨Ne.symm hn.1.2.1,Ne.symm hn.2.1.1,Ne.symm hn.1.2.2,Ne.symm hn.2.1.2⟩
    rcases hi with hi | hi | hi | hi
    · subst i; simp [sectorWord,h0,hi1]
    · subst i; simpa [sectorWord,h0,hi1,Ne.symm hne] using he1
    · subst i; simpa [sectorWord,h0,hi1,hcross.1,hcross.2.1] using hf0
    · subst i; simpa [sectorWord,h0,hi1,hcross.2.2.1,hcross.2.2.2,Ne.symm (ne_of_lt hf)] using hf1

private theorem xor_eq (a b c : Bool) : b = (a ^^ c) ↔ (a ^^ b) = c := by
  cases a <;> cases b <;> cases c <;> decide
private theorem reverse_axes (u v o z b : Bool) :
    (u = (o ^^ b ^^ z) ∧ v = (o ^^ b ^^ z ^^ b)) ↔
      (v = (o ^^ z) ∧ u = (o ^^ z ^^ b)) := by
  cases u <;> cases v <;> cases o <;> cases z <;> cases b <;> decide

/-- Both orientations are reduced algebraically, without enumerating all words. -/
theorem sector_equations_iff (ε : Bool) (d : SectorData) (x : Word) :
    x ∈ (sectorWords ε (sector d)).toFinset ↔ sectorEquations ε d x := by
  rw [canonical_equations_iff]
  rcases d with ⟨⟨i,f,a,b,o⟩,r⟩
  cases r
  · simp only [canonicalEquations,sectorEquations,sector,fixed,varying,
      sourceSectorEquiv_apply,Bool.false_eq_true,ite_false,xor_eq]
  · simp only [canonicalEquations,sectorEquations,sector,fixed,varying,
      sourceSectorEquiv_apply,ite_true]
    rw [reverse_axes]
    simp only [xor_eq]

structure FourFlatData where
  ports : Equiv.Perm Port
  even : SectorData
  odd : SectorData

def FourFlatData.Holds (D : FourFlatData) (x : Word) : Prop :=
  sectorEquations false D.even (fun i => x (D.ports i)) ∨
    sectorEquations true D.odd (fun i => x (D.ports i))

def FourFlatData.support (D : FourFlatData) : Support :=
  transform D.ports.symm (fun _ => false) (Holant.Certificates.NormalizedDihedralQ6.support (sector D.even) (sector D.odd))

theorem FourFlatData.mem_support (D : FourFlatData) (x : Word) :
    x ∈ D.support ↔ D.Holds x := by
  rw [FourFlatData.support,mem_transform]
  have hh : (wordEquiv D.ports.symm (fun _ => false)).symm x = (fun i => x (D.ports i)) := by
    funext i
    simp
  rw [hh]
  simp only [Holant.Certificates.NormalizedDihedralQ6.support,List.toFinset_append,Finset.mem_union,sector_equations_iff,
    FourFlatData.Holds]

/-- The equation has exactly eight words even though its coefficients are
arbitrary; in particular the source hypothesis cannot silently include h=0. -/
private theorem sector_card_four : ∀ (ε : Bool) (d : Sector),
    (sectorWords ε d).toFinset.card = 4 := by decide

private theorem sector_distinguished : ∀ (ε : Bool) (d : Sector) (z w : Bool),
    (sectorWord ε d z w 0 ^^ sectorWord ε d z w 1) = ε := by decide

private theorem mem_sector_distinguished (ε : Bool) (d : Sector) (x : Word)
    (hx : x ∈ (sectorWords ε d).toFinset) : (x 0 ^^ x 1) = ε := by
  simp only [sectorWords,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact sector_distinguished _ _ _ _

theorem support_card_eight (d₀ d₁ : Sector) :
    (support d₀ d₁).card = 8 := by
  have hd : Disjoint (sectorWords false d₀).toFinset (sectorWords true d₁).toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have hh := (mem_sector_distinguished false d₀ x hx).symm.trans
      (mem_sector_distinguished true d₁ x hy)
    cases hh
  rw [support,List.toFinset_append,Finset.card_union_of_disjoint hd,
    sector_card_four,sector_card_four]

theorem FourFlatData.card (D : FourFlatData) : D.support.card = 8 := by
  unfold FourFlatData.support transform
  rw [Finset.card_image_of_injective _ (wordEquiv _ _).injective,support_card_eight]

/-- Normalized coordinates keep the exact original distinguished endpoints. -/
theorem FourFlatData.distinguished_ne (D : FourFlatData) : D.ports 0 ≠ D.ports 1 :=
  fun h => (by decide : (0 : Port) ≠ 1) (D.ports.injective h)

end Holant.Dihedral.SixToFour
