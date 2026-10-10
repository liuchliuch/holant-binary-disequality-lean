import Holant.Proofs.Hardness.GeneralOddHighTerminalAccess

/-! A minimal actual odd graph closes the decreasing-arity recursion.
It produces an ordinary unary or a universal opposite-charge divisibility
residue. No hardness or tractability conclusion is attached to that residue. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddMinimalTerminal
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open GeneralOddUnaryOrdinary GeneralOddUnarySource
namespace Loops
export Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Loops (NoCuts)
end Loops
namespace Structure
export Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Structure
  (twoConstants ordinary_terminal_decomposition)
end Structure
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

def Available (n : ℕ) : Prop := Odd n ∧ ∃N : Network AlgebraicComplex n,
  Uses N (original G) ∧ Ordinary N ∧ N.denote≠0

structure Minimal where
  arity : ℕ
  odd : Odd arity
  graph : Network AlgebraicComplex arity
  uses : Uses graph (original G)
  ordinary : Ordinary graph
  nonzero : graph.denote≠0
  minimal : ∀m,Available G m → arity≤m

/-- Only an actual original nonzero odd label supplies initial existence. -/
def select (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0) : Minimal G := Classical.choice (by
  classical
  have hex : ∃n,Available G n := ⟨a j.val,ho,Network.corolla (G j),
    (fun _=>⟨j,rfl⟩),(fun e=>Fin.elim0 e),by simpa using hnz⟩
  let n := Nat.find hex
  have hn := Nat.find_spec hex
  obtain ⟨hnodd,N,hNF,hNE,hNz⟩ := hn
  exact ⟨⟨n,hnodd,N,hNF,hNE,hNz,fun m hm=>Nat.find_min' hex hm⟩⟩)

variable (D : Minimal G)

/-- A nonzero Eq contraction would be a strictly smaller actual odd graph. -/
theorem noCuts : Loops.NoCuts D.graph.denote := by
  intro k h p
  let R := reboundary D.graph (finCongr h)
  let N := (reboundary R p).contract Signature.equality
  by_contra hz
  have hnz : N.denote≠0 := by
    intro he
    apply hz
    rw [show N.denote=Signature.contract Signature.equality
      (Tensor.reindex p (Tensor.reindex (finCongr h) D.graph.denote)) from by
        change ((reboundary R p).contract Signature.equality).denote=_
        rw [Network.denote_contract]
        congr 1
        funext x
        simp only [reboundary_denote,R,Tensor.reindex_apply]] at he
    exact he
  have hodd : Odd k := by
    have hd := D.odd
    rw [h] at hd
    obtain ⟨m,hm⟩ := hd
    refine ⟨m-1,?_⟩
    omega
  have hn : Available G k := by
    refine ⟨hodd,N,D.uses,?_,hnz⟩
    intro e
    refine Fin.cases rfl (fun e=>?_) e
    exact D.ordinary e
  have hm := D.minimal k hn
  omega

abbrev endpoint (b : Bool) := sourceKBasis.symm.action D.graph.denote (fun _=>b)

theorem supported_endpoint (hh : 3≤D.arity) : ∃b : Bool,endpoint G D (!b)≠0 := by
  have hd := Structure.ordinary_terminal_decomposition D.graph.denote D.odd hh (noCuts G D)
  by_contra h
  push Not at h
  have h0 := h true
  have h1 := h false
  simp only [Bool.not_true,Bool.not_false] at h0 h1
  change sourceKBasis.symm.action D.graph.denote (fun _=>false)=0 at h0
  change sourceKBasis.symm.action D.graph.denote (fun _=>true)=0 at h1
  have hz : sourceKBasis.symm.action D.graph.denote=0 := by
    rw [hd,h0,h1]
    funext x
    simp [Structure.twoConstants,purePin]
  apply D.nonzero
  have he := congrArg sourceKBasis.action hz
  rw [InvertibleKernel.action_symm_action] at he
  exact he.trans (Signature.coordinateAction_zero _)

/-- Any opposite charge not divisible by the minimal odd arity would produce
an actual smaller odd graph, contradicting minimality. -/
theorem opposite_divisible (b : Bool) (hb : endpoint G D (!b)≠0) :
    GeneralOddHighTerminalGcd.OppositeDivisible G D.arity b := by
  intro k x q hx hq hcharge
  by_contra hdiv
  let P := toNative (Network.corolla (G k))
  let H := toNative D.graph
  have hPF : Uses P (kCoordinates (original G)) :=
    toNative_uses (original G) _ (fun _=>⟨k,rfl⟩)
  have hPX : Native P := toNative_native _ (fun e=>Fin.elim0 e)
  have hHF : Uses H (kCoordinates (original G)) :=
    toNative_uses (original G) _ D.uses
  have hHX : Native H := toNative_native _ D.ordinary
  have hx' : P.denote x≠0 := by simpa [P,toNative_denote,Network.denote_corolla] using hx
  have hy' : H.denote (fun _=>!b)≠0 := by simpa [H,toNative_denote,endpoint] using hb
  have hn : 0<D.arity := by obtain ⟨m,hm⟩ := D.odd; omega
  obtain ⟨hd,hdn,r,t,hr,hrn,htq,he,U,hUF,hUX,hUb,hUv,hUe⟩ :=
    GeneralOddHighTerminalGcd.native_reduction (kCoordinates (original G))
      (by norm_num) b P H hPF hPX hHF hHX x hx' hy' q hq hcharge hn hdiv
  have hodd : Odd (Nat.gcd q D.arity) :=
    Odd.of_dvd_nat D.odd (Nat.gcd_dvd_right _ _)
  have hdiag : sourceKBasis.symm.action (toOrdinary U).denote=U.denote := by
    rw [toOrdinary_denote,InvertibleKernel.symm_action_action]
  have hUnz : (toOrdinary U).denote≠0 := by
    intro hz
    have hh := congrArg sourceKBasis.symm.action hz
    rw [hdiag] at hh
    exact hUb (congrFun (hh.trans (Signature.coordinateAction_zero _)) (fun _=>b))
  have hm := D.minimal (Nat.gcd q D.arity)
    ⟨hodd,toOrdinary U,toOrdinary_uses (original G) U hUF,
      toOrdinary_ordinary U hUX,hUnz⟩
  omega

/-- This closes the decreasing-odd-arity alternative, retaining a genuine
universal divisibility residue instead of an unproved hardness conclusion. -/
theorem classified : D.arity=1 ∨ ∃b : Bool,endpoint G D (!b)≠0 ∧
    GeneralOddHighTerminalGcd.OppositeDivisible G D.arity b := by
  by_cases h : D.arity=1
  · exact .inl h
  · have hh : 3≤D.arity := by obtain ⟨m,hm⟩ := D.odd; omega
    obtain ⟨b,hb⟩ := supported_endpoint G D hh
    exact .inr ⟨b,hb,opposite_divisible G D b hb⟩

/-- The selected graph installs over exactly the original G/Eq coefficient
presentation. Its fixed-template programme has the proved controlled bounds. -/
def actual : GeneralOddHighTerminalAccess.Actual G D.arity :=
  ⟨D.graph,D.uses,D.ordinary⟩

def controlled : GeneralOddHighTerminalAccess.Reduction G (actual G D) :=
  GeneralOddHighTerminalAccess.controlled G (actual G D)

/-- No graph, termination proof, closure witness or classification is supplied
by the caller: one actual original nonzero odd row suffices. -/
theorem source (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0) :
    ∃D : Minimal G,
      (D.arity=1 ∨ ∃b : Bool,endpoint G D (!b)≠0 ∧
        GeneralOddHighTerminalGcd.OppositeDivisible G D.arity b) ∧
      Nonempty (GeneralOddHighTerminalAccess.Reduction G (actual G D)) :=
  ⟨select G j ho hnz,classified G _,⟨controlled G _⟩⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddMinimalTerminal
