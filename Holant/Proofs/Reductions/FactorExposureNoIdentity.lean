import Holant.Proofs.FiniteGroups.Stabilization.FactorExposure
import Holant.Proofs.Reductions.FactorSaturation.Catalogue


noncomputable section
namespace Holant.LocalDrafts.Hardness.FactorExposureNoIdentity
open Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction
open GeneralPowerExposure
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Rewire only the local port numbering. Every original vertex and every
oriented edge occurrence survives, including zero-arity vertices. -/
def reorder {n : ℕ} (N : Network K n)
    (g : Fin N.shape.vertices → AnySignature K)
    (e : ∀v, Fin (g v).1 ≃ Fin (N.shape.arity v)) : Network K n where
  shape := {
    vertices := N.shape.vertices
    arity := fun v => (g v).1
    edges := N.shape.edges
    ports := (Equiv.sigmaCongrRight e).trans N.shape.ports }
  vertex := fun v => (g v).2
  edge := N.edge

@[simp] theorem reorder_port {n : ℕ} (N : Network K n)
    (g : Fin N.shape.vertices → AnySignature K)
    (e : ∀v, Fin (g v).1 ≃ Fin (N.shape.arity v)) (v) (j : Fin (g v).1) :
    (reorder N g e).shape.ports ⟨v,j⟩=N.shape.ports ⟨v,e v j⟩ := rfl

@[simp] theorem reorder_edge {n : ℕ} (N : Network K n)
    (g : Fin N.shape.vertices → AnySignature K)
    (e : ∀v, Fin (g v).1 ≃ Fin (N.shape.arity v)) (k) :
    (reorder N g e).edge k=N.edge k := rfl

theorem reorder_denote {n : ℕ} (N : Network K n)
    (g : Fin N.shape.vertices → AnySignature K)
    (e : ∀v, Fin (g v).1 ≃ Fin (N.shape.arity v))
    (hv : ∀v x, N.vertex v x = (g v).2 (fun j => x (e v j))) :
    (reorder N g e).denote = N.denote := by
  classical
  funext x
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    exact (hv v (N.shape.assignment x z v)).symm
  · rfl

/-- A proof of a local signature permutation selects no new gadget and
introduces no edge. This is the precise replacement needed below. -/
theorem reorder_exists {n : ℕ} (N : Network K n) (F : SignatureFamily K)
    (hv : ∀v, ∃g∈F, ∃e : Fin g.1 ≃ Fin (N.shape.arity v),
      ∀x, N.vertex v x = g.2 (fun j => x (e j)))
    (hX : ∀k, N.edge k=Signature.disequality) :
    ∃M : Network K n,
      M.shape.vertices = N.shape.vertices ∧ M.shape.edges = N.shape.edges ∧
      (∀v, (⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈F) ∧
      (∀k, M.edge k=Signature.disequality) ∧ M.denote=N.denote := by
  classical
  choose g hg e he using hv
  exact ⟨reorder N g e,rfl,rfl,hg,hX,reorder_denote N g e he⟩

/-- Remove exactly the extra grouped-parent label from an ordinary graph.
The source parent is a literal member, so its original ordered ports suffice;
no I, scalar normalization, cap, or free wire is introduced. -/
theorem ungroup {f a b : AnySignature K} (split : ProperSplit f a b)
    (F : SignatureFamily K) (hf : f∈F) {n : ℕ} (N : Network K n)
    (hN : ∀v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈
      insert ⟨a.1+b.1,split.grouped⟩ F)
    (hX : ∀k, N.edge k=Signature.disequality) :
    ∃M : Network K n,
      M.shape.vertices=N.shape.vertices ∧ M.shape.edges=N.shape.edges ∧
      (∀v, (⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈F) ∧
      (∀k, M.edge k=Signature.disequality) ∧ M.denote=N.denote := by
  have hlocal : ∀(u : AnySignature K), u∈insert ⟨a.1+b.1,split.grouped⟩ F →
      ∃g∈F, ∃e : Fin g.1 ≃ Fin u.1, ∀x, u.2 x=g.2 (fun j => x (e j)) := by
    intro u hu
    rcases Set.mem_insert_iff.mp hu with rfl|hu
    · exact ⟨f,hf,split.ports.symm.trans finSumFinEquiv,fun _ => rfl⟩
    · exact ⟨u,hu,Equiv.refl _,fun _ => rfl⟩
  exact reorder_exists N F (fun v => hlocal _ (hN v)) hX

/-- Positive power exposure from the real root label. The nonzero carrier
is for the discarded scaled RIGHT factor. The stored left-factor carrier
alone would not justify this step. The old carrier construction supplies
the correct witness internally from the same mixed support. -/
theorem left_power {f a b : AnySignature K} (split : ProperSplit f a b)
    (F : SignatureFamily K) (htwo : (2:K)≠0)
    (hs : GeneralCarrierExistence.MixedSupport F) (hn : f.2≠0) (hf : f∈F) :
    ∃r : ℕ, 0<r ∧ ∃c : K, c≠0 ∧ ∃N : Network K (r*a.1),
      (∀v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈F) ∧
      (∀e, N.edge e=Signature.disequality) ∧
      N.denote=fun x => c*Carrier.blockPower a.2 r x := by
  let U : SignatureFamily K := insert ⟨a.1+b.1,split.grouped⟩ F
  have ht : (⟨a.1+b.1,Signature.tensor a.2 split.scaledRight⟩ : AnySignature K)∈U := by
    rw [←split.grouped_eq]
    exact Set.mem_insert _ _
  obtain ⟨r,hr,c,hc,N,hU,hX,hvalue⟩ := ordinary_power U htwo
    (mixedSupport_mono (Set.subset_insert _ _) hs) a.2 split.scaledRight
      split.right_pos (split.scaledRight_nonzero hn) ht
  obtain ⟨M,_,_,hM,hMX,hMv⟩ := ungroup split F hf N hU hX
  exact ⟨r,hr,c,hc,M,hM,hMX,hMv.trans hvalue⟩

theorem labelled {f a b : AnySignature K} (split : ProperSplit f a b)
    {s : ℕ} {A : ℕ → ℕ} (G : (i : Fin s) → Signature K (A i.val))
    (htwo : (2:K)≠0)
    (hs : GeneralCarrierExistence.MixedSupport
      (Set.range (fun i => (⟨A i.val,G i⟩ : AnySignature K))))
    (hn : f.2≠0)
    (hf : f∈Set.range (fun i => (⟨A i.val,G i⟩ : AnySignature K))) :
    Nonempty (PowerMacro G a.2) := by
  obtain ⟨r,hr,c,hc,N,hN,hX,hv⟩ := left_power split _ htwo hs hn hf
  let lab := Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses A G N hN (0:Fin 1)
  refine ⟨⟨r,hr,c,hc,N,lab,?_⟩⟩
  exact (Holant.Complexity.BinaryInterpolation.Chains.labellingOfUses_denote A G N hN hX
    (0:Fin 1) (fun _ => Signature.disequality) rfl).trans hv

section Catalogue
open FactorSaturation
variable {s : ℕ} (roots : Fin s → AnySignature AlgebraicComplex)
variable (hn : ∀i, (roots i).2≠0)
variable (hs : GeneralCarrierExistence.MixedSupport (Set.range roots))

include hs in
/-- The root-to-occurrence split comes from the SAME stored tree, with all
its composed units and ports. No intermediate factor is treated as an oracle
label of the original family. Duplicate occurrences remain distinct slots. -/
theorem power_exists (j : Fin (addedCount roots hn)) :
    Nonempty (PowerMacro (original roots hn) (next roots hn j.val)) := by
  change Nonempty (PowerMacro (original roots hn) (lookup roots hn (s+j.val)).2)
  rw [lookup_new]
  let u := enumerate roots hn j
  obtain ⟨b,⟨split⟩⟩ := proper_split (tree roots hn u.1) u.2
  apply labelled split (original roots hn) (by norm_num)
  · rwa [original_family]
  · exact hn u.1
  · rw [original_family]
    exact ⟨u.1,rfl⟩

def power (j : Fin (addedCount roots hn)) :
    PowerMacro (original roots hn) (next roots hn j.val) :=
  Classical.choice (power_exists roots hn hs j)
end Catalogue
end Holant.LocalDrafts.Hardness.FactorExposureNoIdentity
