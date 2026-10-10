import Holant.Proofs.Hardness.GeneralEOPinnedDescentOperations
import Holant.Proofs.Hardness.EOBinaryPlaneOpen
import Holant.Proofs.Hardness.SelfDualPinObstruction

/-! Literal two-copy mating with every tail port joined by a native X edge.
The four ordered boundary ports are the two prefix ports of each copy. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedMating
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace O
export GeneralEOPinnedDescentOperations (word front front_word word_weight)
end O
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def layout : Fin (n+2) ≃ (Fin 2 ⊕ Fin n) := O.front.trans finSumFinEquiv.symm

def shape (n : ℕ) : NetworkShape 4 where
  vertices := 2
  arity _ := n+2
  edges := n
  ports := (Equiv.sigmaEquivProd (Fin 2) (Fin (n+2))).trans
    ((Equiv.prodCongr (Equiv.refl _) layout).trans
      ((Equiv.prodSumDistrib _ _ _).trans
        (Equiv.sumCongr finProdFinEquiv
          ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)))))

variable {K : Type*} [CommSemiring K]

def network (f : Signature K (n+2)) : Network K 4 where
  shape := shape n
  vertex _ := f
  edge _ := Signature.disequality

def output (f : Signature K (n+2)) : Signature K 4 := fun x =>
  ∑ z : Fin n → Bool, f (O.word (x 0) (x 1) z) *
    f (O.word (x 2) (x 3) (fun k => !(z k)))

theorem assignment (x : Fin 4 → Bool) (z : (Fin n × Bool) → Bool) (v : Fin 2) :
    (shape n).assignment x z v = O.word
      (x (finProdFinEquiv (v,(0 : Fin 2)))) (x (finProdFinEquiv (v,(1 : Fin 2))))
      (fun k => z (k,finTwoEquiv v)) := by
  rw [← O.front_word]
  funext k
  obtain ⟨q,hq⟩ := (@finSumFinEquiv 2 n).surjective (O.front k)
  change Sum.elim x z
    ((Equiv.sumCongr finProdFinEquiv
      ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)))
      ((Equiv.prodSumDistrib _ _ _) (v,finSumFinEquiv.symm (O.front k)))) = _
  rw [← hq]
  cases q with
  | inl b =>
    fin_cases b <;> simp [Equiv.prodSumDistrib]
  | inr t => simp [Equiv.prodSumDistrib]

theorem denote (f : Signature K (n+2)) : (network f).denote = output f := by
  funext x
  rw [EOBinaryPlaneOpen.native_sum (network f) (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro z _
  change (∏ v : Fin 2, f ((shape n).assignment x
    (fun e => if e.2 then !(z e.1) else z e.1) v)) = _
  rw [Fin.prod_univ_two,assignment,assignment]
  rfl

theorem output_swap (f : Signature K (n+2)) (a b c d : Bool) :
    output f ![a,b,c,d] = output f ![c,d,a,b] := by
  unfold output
  apply Fintype.sum_equiv (SelfDualPinObstruction.flipEquiv (Fin n))
  intro z
  change f (O.word a b z) * f (O.word c d (fun k => !(z k))) =
    f (O.word c d (fun k => !(z k))) * f (O.word a b (fun k => !(!(z k))))
  simp only [Bool.not_not]
  exact mul_comm _ _

theorem central (f : Signature K (n+2)) (he : Signature.CentralSupport f) :
    Signature.CentralSupport (network f).denote := by
  intro x hx
  rw [denote]
  apply Finset.sum_eq_zero
  intro z _
  by_cases h0 : f (O.word (x 0) (x 1) z) = 0
  · simp only [h0,zero_mul]
  by_cases h1 : f (O.word (x 2) (x 3) (fun k => !(z k))) = 0
  · simp only [h1,mul_zero]
  have w0 : 2 * weight (O.word (x 0) (x 1) z) = n+2 := by
    by_contra hh
    exact h0 (he _ hh)
  have w1 : 2 * weight (O.word (x 2) (x 3) (fun k => !(z k))) = n+2 := by
    by_contra hh
    exact h1 (he _ hh)
  rw [O.word_weight] at w0 w1
  have wz := weight_compl_add z
  have wx : weight x = (if x 0 then 1 else 0) + (if x 1 then 1 else 0) +
      (if x 2 then 1 else 0) + (if x 3 then 1 else 0) := by
    simp only [weight,Fin.sum_univ_four]
  exact False.elim (hx (by omega))

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))
variable (j : Fin s) (f : Signature K (n+2))
variable (hj : (⟨a j.val,G j⟩ : AnySignature K) = ⟨n+2,f⟩)

def labels : Labelling (network f).shape s 1 a where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst hj
  edge _ := 0

theorem exact_labels : LabelledNetwork.Exact G (network f) (labels G j f hj) :=
  fun _ => hj

theorem native : ∀ e, (network f).edge e = Signature.disequality := fun _ => rfl

theorem counts : (network f).shape.vertices = 2 ∧ (network f).shape.edges = n := ⟨rfl,rfl⟩

/-- Move local ports in the incidence map; the vertex table stays original. -/
def permuted (f : Signature K (n+2)) (e : Equiv.Perm (Fin (n+2))) : Network K 4 where
  shape := { shape n with ports :=
    (Equiv.sigmaCongrRight (fun _ : Fin 2 => e.symm)).trans (shape n).ports }
  vertex _ := f
  edge _ := Signature.disequality

theorem permuted_denote (f : Signature K (n+2)) (e : Equiv.Perm (Fin (n+2))) :
    (permuted f e).denote=output (fun x => f (x ∘ e.symm)) := by
  rw [← denote]
  rfl

def permutedLabels (e : Equiv.Perm (Fin (n+2))) : Labelling (permuted f e).shape s 1 a where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst hj
  edge _ := 0

theorem permuted_exact (e : Equiv.Perm (Fin (n+2))) :
    LabelledNetwork.Exact G (permuted f e) (permutedLabels G j f hj e) := fun _ => hj

theorem permuted_native (e : Equiv.Perm (Fin (n+2))) :
    ∀ k,(permuted f e).edge k=Signature.disequality := fun _ => rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedMating
