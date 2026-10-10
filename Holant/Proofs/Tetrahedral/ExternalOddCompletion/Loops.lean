import Holant.Proofs.Reductions.GeneralExtraction.NamedContraction
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence
import Mathlib.Data.List.Find


noncomputable section
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Loops
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val)) (j : Fin s)

/-- One occurrence of the selected ORIGINAL label. Only its boundary-to-edge
incidence is changed; no vertex or local port is replaced. -/
structure Frame (j : Fin s) (n : ℕ) where
  shape : NetworkShape n
  one : shape.vertices = 1
  originalArity : ∀ v, shape.arity v = a j.val

namespace Frame
variable {j : Fin s} {n : ℕ}

def labels (D : Frame (a:=a) j n) : Labelling D.shape s 1 a where
  vertex _ := j
  vertex_arity v := (D.originalArity v).symm
  edge _ := 0

def network (D : Frame (a:=a) j n) : Network K n :=
  D.labels.sourceNetwork G (fun _ : Fin 1 => Signature.equality)

def initial : Frame (a:=a) j (a j.val) where
  shape := (Network.corolla (G j)).shape
  one := rfl
  originalArity _ := rfl

@[simp] theorem initial_value : ((initial G (j:=j)).network G).denote = G j := by
  have hgraph : ((initial G (j:=j)).network G).denote=(Network.corolla (G j)).denote := by
    apply Network.denote_congr
    · intro v x
      rfl
    · intro e b c
      exact Fin.elim0 e
  exact hgraph.trans (Network.denote_corolla _)

def close {k : ℕ} (D : Frame (a:=a) j (k+2)) (p : Equiv.Perm (Fin (k+2))) :
    Frame (a:=a) j k where
  shape := ((reboundary (D.network G) p).contract Signature.equality).shape
  one := D.one
  originalArity := D.originalArity

@[simp] theorem close_edges {k : ℕ} (D : Frame (a:=a) j (k+2))
    (p : Equiv.Perm (Fin (k+2))) :
    (D.close G p).shape.edges = D.shape.edges+1 := rfl

/-- This equality uses Eq on the NEW loop and on every old loop. The existing
native-X contraction theorem is not substituted for this statement. -/
theorem close_value {k : ℕ} (D : Frame (a:=a) j (k+2))
    (p : Equiv.Perm (Fin (k+2))) :
    ((D.close G p).network G).denote =
      Signature.contract Signature.equality (Tensor.reindex p (D.network G).denote) := by
  have hlabels : ((D.close G p).network G).denote =
      ((reboundary (D.network G) p).contract Signature.equality).denote := by
    apply Network.denote_congr
    · intro v x
      rfl
    · intro e b c
      refine Fin.cases ?_ (fun e => ?_) e <;> rfl
  rw [hlabels,Network.denote_contract]
  congr 1
  funext x
  exact reboundary_denote (D.network G) p x

end Frame

/-- All ordered pair closures are zero, including pair choices at a single
vertex. The transport only reconciles the displayed arity with `k+2`. -/
def NoCuts {n : ℕ} (f : Signature K n) : Prop :=
  ∀ (k : ℕ) (h : n=k+2) (p : Equiv.Perm (Fin (k+2))),
    Signature.contract Signature.equality
      (Tensor.reindex p (Tensor.reindex (finCongr h) f)) = 0

def cut {k : ℕ} (D : Frame (a:=a) j (k+2)) (p : Equiv.Perm (Fin (k+2))) :=
  Signature.contract Signature.equality (Tensor.reindex p (D.network G).denote)

/-- Finite fixed-family installation data, rather than a chosen desired cap.
This list order is stored once; the later graph compiler never scans it. -/
def firstCut {k : ℕ} (D : Frame (a:=a) j (k+2)) :
    Option (Equiv.Perm (Fin (k+2))) :=
  (Finset.univ : Finset (Equiv.Perm (Fin (k+2)))).toList.find?
    (fun p => decide (cut G j D p ≠ 0))

theorem firstCut_nonzero {k : ℕ} (D : Frame (a:=a) j (k+2))
    (p : Equiv.Perm (Fin (k+2))) (h : firstCut G j D=some p) : cut G j D p ≠ 0 := by
  have hp := List.find?_some h
  simpa only [decide_eq_true_eq] using hp

theorem firstCut_none {k : ℕ} (D : Frame (a:=a) j (k+2))
    (h : firstCut G j D=none) : ∀ p,cut G j D p=0 := by
  have hn := List.find?_eq_none.mp h
  intro p
  have hp := hn p (by simp)
  simpa only [decide_eq_true_eq,not_ne_iff] using hp

/-- The output of the concrete scan/descent. Conservation counts real loop
edges, so parity and the number of source occurrences are not folklore claims. -/
structure Descendant {n : ℕ} (D : Frame (a:=a) j n) where
  arity : ℕ
  frame : Frame (a:=a) j arity
  odd : Odd arity
  nonzero : (frame.network G).denote ≠ 0
  arity_le : arity ≤ n
  conservation : arity+2*frame.shape.edges = n+2*D.shape.edges
  stopped : NoCuts (frame.network G).denote

/-- A finite, terminating installation procedure. Each successful branch adds
an ACTUAL ordinary loop and recurses at arity two smaller. The failed branch
proves that every ordered pair, rather than just the first trial, vanished. -/
def descend (n : ℕ) (D : Frame (a:=a) j n) (ho : Odd n)
    (hnz : (D.network G).denote ≠ 0) : Descendant G j D := by
  have build : ∀ n (D : Frame (a:=a) j n), Odd n →
      (D.network G).denote ≠ 0 → Descendant G j D := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro D ho hnz
      by_cases hs : n<2
      · have he : n=1 := by
          obtain ⟨t,ht⟩ := ho
          omega
        subst n
        exact {
          arity := 1
          frame := D
          odd := ho
          nonzero := hnz
          arity_le := le_rfl
          conservation := rfl
          stopped := by
            intro k hk p
            omega }
      · generalize hk : n-2 = k
        have he : n=k+2 := by omega
        subst n
        cases hc : firstCut G j D with
        | none =>
          exact {
            arity := k+2
            frame := D
            odd := ho
            nonzero := hnz
            arity_le := le_rfl
            conservation := rfl
            stopped := by
              intro l hl p
              have he : k=l := by omega
              subst l
              have hi : finCongr hl = Equiv.refl (Fin (k+2)) := by
                ext i
                rfl
              rw [hi,Tensor.reindex_refl]
              exact firstCut_none G j D hc p }
        | some p =>
          have hk : Odd k := by
            obtain ⟨t,ht⟩ := ho
            have htpos : 0<t := by omega
            exact ⟨t-1,by omega⟩
          have hcut : ((D.close G p).network G).denote ≠ 0 := by
            rw [Frame.close_value]
            exact firstCut_nonzero G j D p hc
          let R := ih k (by omega) (D.close G p) hk hcut
          exact {
            arity := R.arity
            frame := R.frame
            odd := R.odd
            nonzero := R.nonzero
            arity_le := R.arity_le.trans (by omega)
            conservation := by
              have h := R.conservation
              rw [Frame.close_edges] at h
              omega
            stopped := R.stopped }
  exact build n D ho hnz

def selected (ho : Odd (a j.val)) (hnz : G j ≠ 0) :
    Descendant G j (Frame.initial G (j:=j)) :=
  descend G j (a j.val) (Frame.initial G (j:=j)) ho (by simpa using hnz)

theorem selected_conservation (ho : Odd (a j.val)) (hnz : G j ≠ 0) :
    (selected G j ho hnz).arity+2*(selected G j ho hnz).frame.shape.edges=a j.val := by
  have h := (selected G j ho hnz).conservation
  change _ = a j.val + 2 * 0 at h
  simpa only [Nat.mul_zero,Nat.add_zero] using h

theorem selected_loop_bound (ho : Odd (a j.val)) (hnz : G j ≠ 0) :
    (selected G j ho hnz).frame.shape.edges ≤ (a j.val-1)/2 := by
  have h := selected_conservation G j ho hnz
  obtain ⟨t,ht⟩ := (selected G j ho hnz).odd
  omega

end Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Loops
