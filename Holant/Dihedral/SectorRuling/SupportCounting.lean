import Holant.Dihedral.SectorRuling.AffineSupport

/-! Exact finite support counting for a third nontrivial pencil sample. Equal
support size and the proved half-intersection bound force full cancellation on
the intersection; this is not assumed as a property of matching products. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
variable {X K : Type*} [Fintype X] [DecidableEq X] [Field K]

def support (f : X → K) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => f x ≠ 0)

@[simp] theorem mem_support (f : X → K) (x : X) : x ∈ support f ↔ f x ≠ 0 := by
  classical
  simp [support]

def combination (a b : K) (f g : X → K) : X → K := fun x => a*f x+b*g x

/-- Both exclusive support regions survive every nontrivial linear combination. -/
theorem exclusive_supports (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (f g : X → K) :
    (support f \ support g) ∪ (support g \ support f) ⊆ support (combination a b f g) := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨hf,hg⟩ := Finset.mem_sdiff.mp hx
    have hf' := (mem_support f x).mp hf
    have hg' : g x=0 := by simpa using hg
    simpa only [mem_support,combination,hg',mul_zero,add_zero] using mul_ne_zero ha hf'
  · obtain ⟨hg,hf⟩ := Finset.mem_sdiff.mp hx
    have hg' := (mem_support g x).mp hg
    have hf' : f x=0 := by simpa using hf
    simpa only [mem_support,combination,hf',mul_zero,zero_add] using mul_ne_zero hb hg'

/-- A third sample of the same support size cancels on the entire nonempty
intersection. Both outside regions and the half-size equality are explicit. -/
theorem third_support_cancellation (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (f g : X → K) (N : ℕ) (hN : 0<N)
    (hf : (support f).card=N) (hg : (support g).card=N)
    (hh : (support (combination a b f g)).card=N)
    (hhalf : 2*(support f ∩ support g).card ≤ N) :
    support (combination a b f g)=(support f \ support g) ∪ (support g \ support f) ∧
      2*(support f ∩ support g).card=N ∧ (support f ∩ support g).Nonempty ∧
      ∀ x ∈ support f ∩ support g,combination a b f g x=0 := by
  classical
  let A := support f
  let B := support g
  let O := (A\B) ∪ (B\A)
  have hd : Disjoint (A\B) (B\A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hO : O.card=(A\B).card+(B\A).card := Finset.card_union_of_disjoint hd
  have h₀ := Finset.card_sdiff_add_card_inter A B
  have h₁ := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at h₁
  have hsub : O ⊆ support (combination a b f g) := exclusive_supports a b ha hb f g
  have hle := Finset.card_le_card hsub
  have hcard : O.card=N := by change A.card=N at hf; change B.card=N at hg; change 2*(A∩B).card ≤ N at hhalf; omega
  have he : O=support (combination a b f g) := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hi : 2*(support f∩support g).card=N := by
    change A.card=N at hf
    change B.card=N at hg
    change 2*(A∩B).card=N
    omega
  refine ⟨he.symm,hi,Finset.card_pos.mp (by omega),?_⟩
  intro x hx
  by_contra hn
  have hm : x ∈ O := he.symm ▸ (mem_support _ x).mpr hn
  rcases Finset.mem_union.mp hm with hm|hm
  · exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_inter.mp hx).2
  · exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_inter.mp hx).1

end Holant.Dihedral.SectorRuling
