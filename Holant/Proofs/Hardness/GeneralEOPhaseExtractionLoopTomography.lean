import Holant.Proofs.Hardness.GeneralEOPhaseExtractionCoordinates
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSigns

/-! Native contractions determine every central tensor of arity at least three.
The reconstruction uses three actual coordinate permutations and one native
self-loop for each measurement. In particular, no pins or signed edges occur. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionLoopTomography
open Holant
namespace P
export GeneralEOPhaseExtractionCoordinates (columns column_equations prefix_three tail3)
end P
namespace T
export GeneralEOPhaseExtractionStep (Pair perm triple leftWord rightWord perm_left perm_right)
end T
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace F
export SelfDualPinObstruction (flip SelfDual)
end F
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote)
end R
namespace D
export GeneralEOPhaseExtractionDistance (loop loop_denote)
end D
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def merge (f : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) : Signature ℂ n :=
  fun x => f (O.word false true x ∘ e)+f (O.word true false x ∘ e)

theorem merge_denote (S : Network ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) :
    (D.loop (R.reboundary S e)).denote=merge S.denote e := by
  funext x
  rw [D.loop_denote,R.reboundary_denote]
  rfl

theorem merge_triple (f : Signature ℂ (n+3)) (p : T.Pair) (x : Fin n → Bool) :
    merge f (T.perm p) (Fin.cons true x)=f (T.leftWord x p)+f (T.rightWord x p) := by
  change f (T.triple false true true x ∘ T.perm p)+
    f (T.triple true false true x ∘ T.perm p)=_
  rw [T.perm_left,T.perm_right]

theorem reconstruct_triple (f : Signature ℂ (n+3)) (x : Fin n → Bool) :
    2*f (T.triple false true true x)=
      merge f (T.perm .firstSecond) (Fin.cons true x)+
      merge f (T.perm .firstThird) (Fin.cons true x)-
      merge f (T.perm .secondThird) (Fin.cons true x) := by
  simp only [merge_triple,T.leftWord,T.rightWord]
  ring

theorem balanced_prefix (x : Fin (n+3) → Bool) (hx : 2*weight x=n+3) :
    ∃e : Equiv.Perm (Fin (n+3)),
      x ∘ e=T.triple false true true (P.tail3 (x ∘ e)) := by
  have h := P.column_equations x x
  have hz : (P.columns x x false true).card=0 := by
    simp [P.columns]
  have hz' : (P.columns x x true false).card=0 := by
    simp [P.columns]
  have h00 : 0<(P.columns x x false false).card := by omega
  have h11 : 1<(P.columns x x true true).card := by omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp h00
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp h11
  simp only [P.columns,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj hk
  have hij : i≠j := by rintro rfl; simp_all
  have hik : i≠k := by rintro rfl; simp_all
  let v : Fin 3 → Fin (n+3) := ![i,j,k]
  have hv : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [v]
  obtain ⟨h,e,he⟩ := GeneralEOCentralHolePatterns.exists_prefix_permutation v hv
  refine ⟨e,P.prefix_three (x ∘ e) h ?_⟩
  funext q
  simp only [Function.comp_apply,he]
  fin_cases q <;> simp [v,hi.1,hj.1,hk.1]

theorem merge_comp (f : Signature ℂ (n+2)) (e p : Equiv.Perm (Fin (n+2))) :
    merge (fun x => f (x ∘ e)) p=merge f (e.trans p) := rfl

/-- Three pair sums recover a coefficient. All balanced coefficients admit
such a coordinate arrangement; unbalanced coefficients are already zero. -/
theorem ext_of_merges (f g : Signature ℂ (n+3))
    (hf : Signature.CentralSupport f) (hg : Signature.CentralSupport g)
    (h : ∀e,merge f e=merge g e) : f=g := by
  funext x
  by_cases hx : 2*weight x=n+3
  · obtain ⟨e,he⟩ := balanced_prefix x hx
    let f' : Signature ℂ (n+3) := fun z => f (z ∘ e.symm)
    let g' : Signature ℂ (n+3) := fun z => g (z ∘ e.symm)
    have h' (p : Equiv.Perm (Fin (n+3))) : merge f' p=merge g' p :=
      h (e.symm.trans p)
    have hh : 2*f' (T.triple false true true (P.tail3 (x ∘ e)))=
        2*g' (T.triple false true true (P.tail3 (x ∘ e))) := by
      rw [reconstruct_triple,reconstruct_triple,h',h',h']
    have hfg := mul_left_cancel₀ (by norm_num : (2 : ℂ)≠0) hh
    rw [←he] at hfg
    simpa [f',g',Function.comp_def] using hfg
  · rw [hf x hx,hg x hx]

theorem merge_flip (f : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) :
    merge (fun x => f (F.flip x)) e=fun x => merge f e (F.flip x) := by
  funext x
  have hf (u v : Bool) : F.flip (O.word u v x ∘ e)=
      O.word (!u) (!v) (F.flip x) ∘ e := by
    change F.flip (O.word u v x) ∘ e=_
    rw [GeneralEOPhaseExtractionSigns.flip_word]
  simp only [merge,hf,Bool.not_false,Bool.not_true]
  exact add_comm _ _

theorem selfDual_of_merges (f : Signature ℂ (n+3))
    (hf : Signature.CentralSupport f) (h : ∀e,F.SelfDual (merge f e)) : F.SelfDual f := by
  have hfc : Signature.CentralSupport (fun x => f (F.flip x)) := by
    intro x hx
    apply hf
    have hw : weight (F.flip x)+weight x=n+3 := weight_compl_add x
    change 2*weight x≠n+3 at hx
    change 2*weight (F.flip x)≠n+3
    omega
  have he : (fun x => f (F.flip x))=f := by
    apply ext_of_merges _ _ hfc hf
    intro e
    rw [merge_flip]
    exact funext (h e)
  exact congrFun he

/-- Physical form: symmetry of every native one-loop child forces symmetry
of the original graph. The child is reboundary plus a genuine native loop. -/
theorem selfDual_of_native_loops (S : Network ℂ (n+3))
    (hS : Signature.CentralSupport S.denote)
    (h : ∀e : Equiv.Perm (Fin (n+3)),F.SelfDual (D.loop (R.reboundary S e)).denote) : F.SelfDual S.denote := by
  apply selfDual_of_merges S.denote hS
  intro e
  rw [←merge_denote]
  exact h e

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionLoopTomography
