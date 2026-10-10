import Holant.Observability.Consequences

/-!
The full source grammar allows both explicit I edges and native X edges.
Every such finite ordered chain is translated to the native grammar, with
literal equality vertices supplying the exact `X I X = I` replacement.
The two actual transfer ranges (not merely their spans) are proved equal.
-/
namespace Holant.Observability

noncomputable section

/-- The source's full finite ordered-chain grammar, allowing each joining
edge independently to be literal I or native X. -/
inductive LinkedChain (ι : Type*) where
  | atom (i : ι)
  | identity
  | exchange
  | series (edge : EdgeKind) (left right : LinkedChain ι)
  | reverse (chain : LinkedChain ι)

namespace LinkedChain

variable {ι : Type*}

/-- Every physical edge retains its actual I/X table and both incident bits. -/
def evaluate (family : ι → Mat) : LinkedChain ι → Mat
  | .atom i => family i
  | .identity => Signature.equality
  | .exchange => Signature.disequality
  | .series edge L R => Kernel.join edge.value
      (evaluate family L) (Kernel.transpose (evaluate family R))
  | .reverse C => Kernel.transpose (evaluate family C)

def transfer (family : ι → Mat) (chain : LinkedChain ι) : Mat :=
  Kernel.mul (evaluate family chain) Signature.disequality

/-- Replace each I edge by its explicit native-X/literal-I/native-X chain. -/
def toNative : LinkedChain ι → Chain ι
  | .atom i => .atom i
  | .identity => .identity
  | .exchange => .exchange
  | .series .equality L R => Chain.equalitySeries (toNative L) (toNative R)
  | .series .disequality L R => .series (toNative L) (toNative R)
  | .reverse C => .reverse (toNative C)

/-- Native-only chains are literally a subgrammar of the source grammar. -/
def ofNative : Chain ι → LinkedChain ι
  | .atom i => .atom i
  | .identity => .identity
  | .exchange => .exchange
  | .series L R => .series .disequality (ofNative L) (ofNative R)
  | .reverse C => .reverse (ofNative C)

/-- Expansion preserves the complete physical table, with no scalar loss. -/
theorem evaluate_toNative (family : ι → Mat) (chain : LinkedChain ι) :
    Chain.evaluate family (toNative chain) = evaluate family chain := by
  induction chain with
  | atom i => rfl
  | identity => rfl
  | exchange => rfl
  | series edge L R hL hR =>
    cases edge with
    | equality =>
      simpa only [toNative, evaluate, EdgeKind.value, hL, hR] using
        Chain.evaluate_equalitySeries family (toNative L) (toNative R)
    | disequality =>
      change Kernel.join Signature.disequality (Chain.evaluate family (toNative L))
        (Kernel.transpose (Chain.evaluate family (toNative R))) = _
      rw [hL, hR]
      rfl
  | reverse C hC =>
    change Kernel.transpose (Chain.evaluate family (toNative C)) = _
    rw [hC]
    rfl

theorem evaluate_ofNative (family : ι → Mat) (chain : Chain ι) :
    evaluate family (ofNative chain) = Chain.evaluate family chain := by
  induction chain with
  | atom i => rfl
  | identity => rfl
  | exchange => rfl
  | series L R hL hR =>
    change Kernel.join Signature.disequality (evaluate family (ofNative L))
      (Kernel.transpose (evaluate family (ofNative R))) = _
    rw [hL, hR]
    rfl
  | reverse C hC =>
    change Kernel.transpose (evaluate family (ofNative C)) = _
    rw [hC]
    rfl

theorem transfer_toNative (family : ι → Mat) (chain : LinkedChain ι) :
    Chain.transfer family (toNative chain) = transfer family chain := by
  simp only [Chain.transfer, transfer, evaluate_toNative]

theorem transfer_ofNative (family : ι → Mat) (chain : Chain ι) :
    transfer family (ofNative chain) = Chain.transfer family chain := by
  simp only [Chain.transfer, transfer, evaluate_ofNative]

/-- Exact grammar equivalence at the set of actual transfer tables. -/
theorem transfer_range (family : ι → Mat) :
    Set.range (transfer family) = Set.range (Chain.transfer family) := by
  ext A
  constructor
  · rintro ⟨chain, rfl⟩
    exact ⟨toNative chain, transfer_toNative family chain⟩
  · rintro ⟨chain, rfl⟩
    exact ⟨ofNative chain, transfer_ofNative family chain⟩

/-- Explicit flattened graph for every mixed-I/X source chain. -/
def network (family : ι → Mat) (chain : LinkedChain ι) : Network ℂ 2 :=
  Chain.network family (toNative chain)

theorem network_denote (family : ι → Mat) (chain : LinkedChain ι) :
    (network family chain).denote = binarySignature (evaluate family chain) := by
  rw [network, Chain.network_denote, evaluate_toNative]

theorem network_uses (family : ι → Mat) (chain : LinkedChain ι) :
    uses (network family chain) (chainResources family) :=
  Chain.network_uses family (toNative chain)

theorem network_native (family : ι → Mat) (chain : LinkedChain ι) :
    native (network family chain) := Chain.network_native family (toNative chain)

theorem realizes (family : ι → Mat) (chain : LinkedChain ι) :
    Gadget.Realizes (chainResources family) .disequality
      (binarySignature (evaluate family chain)) := by
  rw [← evaluate_toNative]
  exact Chain.realizes family (toNative chain)

theorem realizes_transfer (family : ι → Mat) (chain : LinkedChain ι) :
    Gadget.Realizes (chainResources family) .disequality
      (binarySignature (transfer family chain)) := by
  rw [← transfer_toNative]
  exact Chain.realizes_transfer family (toNative chain)

end LinkedChain

variable {ι : Type*}

/-- Source `def:effective-kernel-algebra`: complex span of all finite actual ordered chain
transfers, with fixed supplied binary representatives, both link types,
and physical port reversal. -/
def linkedChainSpan (family : ι → Mat) : Submodule ℂ Mat :=
  Submodule.span ℂ (Set.range (LinkedChain.transfer family))

/-- The native grammar loses no source chains; its closure was proved
constructively and every added I-edge has an exact native-chain expansion. -/
theorem linkedChainSpan_eq (family : ι → Mat) :
    linkedChainSpan family = chainSpan family := by
  simp only [linkedChainSpan, chainSpan, LinkedChain.transfer_range]

/-- Full-source Theorem 5.17, together with explicit gadget provenance for
every actual transfer generating the span. The supplied family is arbitrary,
so fixed actual representatives from a complete retained group are a case. -/
theorem linked_dressed_kernel_observability (family : ι → Mat) :
    (linkedChainSpan family = ixSpan ∨ linkedChainSpan family = ⊤) ∧
    frobeniusOrthogonal ixSpan = {A | ∃ u v : ℂ, A = invisible u v} ∧
    ∀ chain : LinkedChain ι, Gadget.Realizes (chainResources family) .disequality
      (binarySignature (LinkedChain.transfer family chain)) := by
  refine ⟨?_, ixSpan_frobenius_complement, LinkedChain.realizes_transfer family⟩
  rw [linkedChainSpan_eq]
  exact realizable_binary_kernel_span family

end
end Holant.Observability
