import Holant.Proofs.Hardness.GeneralEODEQProducerStep

/-! The isolated interval is reduced to four boundary ports using only
literal paired pins, original vertices, permutations, and native X loops. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerReduction
open Holant Holant.Complexity FixedGadgetSubstitution
open GeneralEODEQProducerCore
namespace S
export GeneralEODEQProducerStep (pinnedPair loop loopPair loop_central)
end S
namespace L
export GeneralEOPinnedDescentLabels (pinnedLabels pinned_exact pinned_native)
end L
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))

structure Reduced where
  network : Network K 4
  labels : Labelling network.shape s 1 a
  exact : LabelledNetwork.Exact G network labels
  native : ∀e,network.edge e=Signature.disequality
  central : Signature.CentralSupport network.denote
  pair : Pair network.denote

variable (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature K)=⟨2,GeneralEOPinnedDescentNetwork.directed01⟩)

include j hj in
/-- The output contains a literal graph and labels over precisely the input
palette. Every recursive call strictly removes two boundary coordinates. -/
theorem reduce : ∀ (n : ℕ) (T : Network K n) (TL : Labelling T.shape s 1 a),
    LabelledNetwork.Exact G T TL → (∀e,T.edge e=Signature.disequality) →
    Signature.CentralSupport T.denote → Pair T.denote → Nonempty (Reduced G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T TL hE hN hC p
    have hcn := central_word T.denote hC p.left p.left_supported
    have hd := p.distant
    have hn := distance_le p.left p.right
    by_cases heq : n=4
    · subst n
      exact ⟨⟨T,TL,hE,hN,hC,p⟩⟩
    have hhigh : 6≤n := by omega
    obtain ⟨m,rfl⟩ : ∃m,n=m+2 := ⟨n-2,by omega⟩
    have hmlt : m<m+2 := by omega
    have hcm := central_word T.denote hC p.right p.right_supported
    by_cases hlt : D.distance p.left p.right<m+2
    · obtain ⟨e,ha,hb⟩ := common_prefix p.left p.right hcn hcm hlt
      let U := N.reboundary T e.symm
      let UL := N.reboundaryLabels T TL e.symm
      let q := Pair.reboundary T p e
      let c := E.tail2 (p.left ∘ e)
      let d := E.tail2 (p.right ∘ e)
      have hqa : q.left=O.word false true c := ha
      have hqb : q.right=O.word false true d := hb
      have hcU : Signature.CentralSupport U.denote := E.reboundary_central T e hC
      exact ih m hmlt (O.pinned U false) (L.pinnedLabels G U UL j hj false)
        (L.pinned_exact G U UL j hj hE false)
        (L.pinned_native U hN false)
        (GeneralEOCentralHoleStep.pinned_central U hcU false)
        (S.pinnedPair U q c d hqa hqb)
    · have hm : D.distance p.left p.right=m+2 := by omega
      have hpne : p.left≠p.right := by
        rintro hp
        rw [hp,D.distance_self] at hd
        omega
      obtain ⟨e,ha,hb⟩ := C.opposite_prefix p.left p.right (by omega) hpne
      let U := N.reboundary T e.symm
      let UL := N.reboundaryLabels T TL e.symm
      let q := Pair.reboundary T p e
      let c := E.tail2 (p.left ∘ e)
      let d := E.tail2 (p.right ∘ e)
      have hqa : q.left=O.word false true c := ha
      have hqb : q.right=O.word true false d := hb
      have hmU : D.distance q.left q.right=m+2 := by
        simpa only [q,Pair.reboundary,C.distance_comp] using hm
      have hdcd : 4≤D.distance c d := by
        rw [hqa,hqb,D.distance_word] at hmU
        norm_num at hmU
        omega
      have hcU : Signature.CentralSupport U.denote := E.reboundary_central T e hC
      exact ih m hmlt (S.loop U) (LabelledNetwork.contract U UL 0 Signature.disequality)
        (LabelledNetwork.exact_contract G U UL hE 0 Signature.disequality)
        (fun i => Fin.cases rfl (fun i => hN i) i)
        (S.loop_central U hcU) (S.loopPair U q c d hqa hqb hmU hdcd)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerReduction
