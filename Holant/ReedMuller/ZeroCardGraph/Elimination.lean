import Holant.ReedMuller.ZeroCardGraph.Graph
import Mathlib.Data.Fintype.Pigeonhole

/-! The zero graph is empty above four ports. The proof uses one actual
supported word to choose a disjoint visible pair, then the literal I/X card
sum contradicts nonvanishing of a nonzero matching card at the zero word. -/
noncomputable section
namespace Holant.ReedMuller.ZeroCardGraph
open Holant
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

 theorem remaining_card_add_two (i j : ι) (hij : i ≠ j) :
    Fintype.card (Remaining i j)+2=Fintype.card ι := by
  classical
  have hset : Finset.univ.filter (fun k : ι => k ≠ i ∧ k ≠ j)=(Finset.univ.erase i).erase j := by
    ext k
    simp [and_comm]
  have h1 := Finset.card_erase_add_one (Finset.mem_univ i)
  have h2 := Finset.card_erase_add_one (by simp [Ne.symm hij] : j ∈ (Finset.univ : Finset ι).erase i)
  simp only [Remaining,Fintype.card_subtype,hset]
  simp only [Finset.card_univ] at h1
  omega

 def NonzeroAtZeroCards (f : Tensor K ι) : Prop :=
  ∀ i j : ι,i ≠ j → ∀ minus : Bool,card f i j minus ≠ 0 → card f i j minus (fun _ => false) ≠ 0

 theorem zero_graph_no_edges (htwo : (2:K) ≠ 0) (f : Tensor K ι) (hf : f ≠ 0)
    (hn : 4<Fintype.card ι) (hcards : NonzeroAtZeroCards f) : ∀ u v : ι,¬(graph f).Adj u v := by
  classical
  intro u v huv
  have hex : ∃ w : ι → Bool,f w ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (funext hh)
  obtain ⟨w,hw⟩ := hex
  have hrem := remaining_card_add_two u v huv.1
  obtain ⟨i,j,hij,hwij⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Remaining u v => w k.val) (by
    simp only [Fintype.card_bool]
    omega)
  have hne : i.val ≠ j.val := fun hh => hij (Subtype.ext hh)
  have hvisible : ¬(card f i.val j.val false=0 ∧ card f i.val j.val true=0) := by
    intro hz
    have he := (graph_zero_cards htwo f i.val j.val hne).mpr hz
    exact he.2 w hw hwij
  obtain ⟨minus,hminus⟩ : ∃ minus : Bool,card f i.val j.val minus ≠ 0 := by
    by_cases hplus : card f i.val j.val false=0
    · exact ⟨true,fun hh => hvisible ⟨hplus,hh⟩⟩
    · exact ⟨false,hplus⟩
  have hzero (b : Bool) : f (sameLift i.val j.val b (fun _ => false))=0 := by
    by_contra hh
    have he := huv.2 (sameLift i.val j.val b (fun _ => false)) hh
    have hu : sameLift i.val j.val b (fun _ => false) u=false :=
      sameLift_remaining _ _ _ _ ⟨u,Ne.symm i.property.1,Ne.symm j.property.1⟩
    have hv : sameLift i.val j.val b (fun _ => false) v=false :=
      sameLift_remaining _ _ _ _ ⟨v,Ne.symm i.property.2,Ne.symm j.property.2⟩
    exact he (hu.trans hv.symm)
  have hc : card f i.val j.val minus (fun _ => false)=0 := by simp [card,hzero]
  exact hcards i.val j.val hne minus hminus hc

 theorem zero_graph_eq_bot (htwo : (2:K) ≠ 0) (f : Tensor K ι) (hf : f ≠ 0)
    (hn : 4<Fintype.card ι) (hcards : NonzeroAtZeroCards f) : graph f=⊥ := by
  ext i j
  simp only [SimpleGraph.bot_adj]
  exact iff_false_intro (zero_graph_no_edges htwo f hf hn hcards i j)

 theorem every_pair_visible (htwo : (2:K) ≠ 0) (f : Tensor K ι) (hf : f ≠ 0)
    (hn : 4<Fintype.card ι) (hcards : NonzeroAtZeroCards f) (i j : ι) (hij : i ≠ j) :
    card f i j false ≠ 0 ∨ card f i j true ≠ 0 := by
  by_contra hh
  push_neg at hh
  exact zero_graph_no_edges htwo f hf hn hcards i j ((graph_zero_cards htwo f i j hij).mpr hh)

end Holant.ReedMuller.ZeroCardGraph
