import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Total

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Canonical packet witnesses and the actual original
bounded accepting paths. Ordinary/halt tokens are checked by the same m.step,
not by a renamed witness predicate. The packet codec gives a genuine bijection.
This does not identify an independent conventional TM presentation with TM2. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

theorem decode_word (word : List Bool) (token : Option Bool)
    (h : Packet.decode word.head? word.tail.head? = some token) :
    word = Packet.encode token++word.tail.tail := by
  cases word with
  | nil => simp [Packet.decode] at h
  | cons first rest =>
    cases rest with
    | nil => simp [Packet.decode] at h
    | cons second rest =>
      cases first <;> cases second <;> fin_cases token <;>
        simp_all [Packet.decode,Packet.encode,Packet.first,Packet.second]

theorem decode_encoded (token : Option Bool) (rest : List Bool) :
    Packet.decode (Packet.encode token++rest).head?
      (Packet.encode token++rest).tail.head? = some token := by
  simpa only [Packet.encode,List.cons_append,List.head?_cons,List.tail_cons] using
    Packet.decode_encode token

theorem packetEval_encoded (n : ℕ) (token : Option Bool) (rest : List Bool)
    (c d : m.Config) (hs : m.step token c = some d) :
    packetEval m acceptControl (n+1) (Packet.encode token++rest) c =
      packetEval m acceptControl n rest d := by
  rw [packetEval,decode_encoded,Option.elim_some,hs,Option.elim_some]
  rfl

/-- Recover actual source edges and an accepting source endpoint from every
accepted word. Extra bytes fail the base case, hence the recovered word is
exactly the canonical encoding of exactly n tokens. -/
theorem packet_accepts_iff (n : ℕ) (word : List Bool) (c : m.Config) :
    packetEval m acceptControl n word c = true ↔
      ∃ tokens d, tokens.length = n ∧ word = tokens.flatMap Packet.encode ∧
        m.TraceValid tokens c d ∧ d.l = none ∧ acceptControl d.var = true := by
  induction n generalizing word c with
  | zero =>
    constructor
    · intro h
      cases word with
      | cons bit rest => simp [packetEval,terminalVerdict] at h
      | nil =>
        cases hl : c.l with
        | some l => simp [packetEval,terminalVerdict,hl] at h
        | none =>
          have ha : acceptControl c.var = true := by
            simpa [packetEval,terminalVerdict,hl] using h
          exact ⟨[],c,rfl,rfl,rfl,hl,ha⟩
    · rintro ⟨tokens,d,hlen,hword,ht,hd,ha⟩
      have htokens : tokens = [] := List.length_eq_zero_iff.mp hlen
      subst tokens
      have hc : c = d := ht
      subst d
      simpa [packetEval,terminalVerdict,hword,hd] using ha
  | succ n ih =>
    constructor
    · intro h
      cases hp : Packet.decode word.head? word.tail.head? with
      | none => simp only [packetEval,hp,Option.elim_none,Bool.false_eq_true] at h
      | some token =>
        cases hs : m.step token c with
        | none => simp only [packetEval,hp,hs,Option.elim_none,Option.elim_some,Bool.false_eq_true] at h
        | some next =>
          have hrest : packetEval m acceptControl n word.tail.tail next = true := by
            simpa only [packetEval,hp,hs,Option.elim_some] using h
          obtain ⟨tokens,d,hlen,hword,ht,hd,ha⟩ := (ih _ _).mp hrest
          refine ⟨token::tokens,d,by simp [hlen],?_,⟨next,hs,ht⟩,hd,ha⟩
          simpa only [List.flatMap_cons,hword] using decode_word word token hp
    · rintro ⟨tokens,d,hlen,hword,ht,hd,ha⟩
      cases tokens with
      | nil => simp at hlen
      | cons token tokens =>
        obtain ⟨next,hs,hrest⟩ := ht
        have hn : tokens.length = n := by simpa only [List.length_cons,Nat.succ.injEq] using hlen
        rw [hword,List.flatMap_cons,packetEval_encoded m acceptControl n token _ c next hs]
        exact (ih _ _).mpr ⟨tokens,d,hn,rfl,hrest,hd,ha⟩

theorem encoded_length (tokens : List (Option Bool)) :
    (tokens.flatMap Packet.encode).length = 2*tokens.length := by
  induction tokens with
  | nil => simp
  | cons token tokens ih => simp [List.flatMap_cons,Packet.encode_length,ih,Nat.mul_succ,Nat.add_comm]

theorem eval_trace (tokens : List (Option Bool)) (c d : m.Config)
    (h : m.TraceValid tokens c d) :
    packetEval m acceptControl tokens.length (tokens.flatMap Packet.encode) c =
      terminalVerdict m acceptControl [] d := by
  induction tokens generalizing c with
  | nil =>
    have hd : c = d := h
    subst d
    rfl
  | cons token tokens ih =>
    obtain ⟨next,hs,ht⟩ := h
    rw [List.length_cons,List.flatMap_cons,packetEval_encoded m acceptControl _ token _ c next hs]
    exact ih next ht

theorem encodeTokens_injective : Function.Injective
    (fun tokens : List (Option Bool) => tokens.flatMap Packet.encode) := by
  intro tokens
  induction tokens with
  | nil =>
    intro other h
    have hl := congrArg List.length h
    rw [encoded_length,encoded_length] at hl
    simp only [List.length_nil, Nat.mul_zero] at hl
    have : other.length = 0 := by omega
    exact (List.length_eq_zero_iff.mp this).symm
  | cons token tokens ih =>
    intro other h
    cases other with
    | nil =>
      have hl := congrArg List.length h
      rw [encoded_length,encoded_length] at hl
      simp at hl
    | cons otherToken other =>
      have hp := congrArg (fun word : List Bool => Packet.decode word.head? word.tail.head?) h
      simp only [List.flatMap_cons,decode_encoded] at hp
      have ht : token = otherToken := Option.some.inj hp
      subst otherToken
      have hr : tokens.flatMap Packet.encode = other.flatMap Packet.encode :=
        List.append_cancel_left (by simpa only [List.flatMap_cons] using h)
      exact congrArg (token :: ·) (ih hr)

abbrev AcceptedPath (n : ℕ) (c : m.Config) :=
  {tokens : Fin n → Option Bool // ∃ d,
    m.TraceValid (List.ofFn tokens) c d ∧ d.l = none ∧ acceptControl d.var = true}

abbrev AcceptedBits (n : ℕ) (c : m.Config) :=
  {bits : Fin (2*n) → Bool // packetEval m acceptControl n (List.ofFn bits) c = true}

noncomputable instance pathFintype (n : ℕ) (c : m.Config) :
    Fintype (AcceptedPath m acceptControl n c) := by
  classical
  unfold AcceptedPath
  infer_instance

noncomputable instance bitsFintype (n : ℕ) (c : m.Config) :
    Fintype (AcceptedBits m acceptControl n c) := by
  classical
  unfold AcceptedBits
  infer_instance

variable {c : m.Config}

def pathBytes (n : ℕ) (p : AcceptedPath m acceptControl n c) : List Bool :=
  (List.ofFn p.val).flatMap Packet.encode

theorem pathBytes_length (n : ℕ) (p : AcceptedPath m acceptControl n c) :
    (pathBytes m acceptControl n p).length = 2*n := by
  rw [pathBytes,encoded_length,List.length_ofFn]

def pathBits (n : ℕ) (p : AcceptedPath m acceptControl n c) : Fin (2*n) → Bool :=
  fun i => (pathBytes m acceptControl n p).get ⟨i.val,by
    rw [pathBytes_length]
    exact i.isLt⟩

theorem pathBits_word (n : ℕ) (p : AcceptedPath m acceptControl n c) :
    List.ofFn (pathBits m acceptControl n p) = pathBytes m acceptControl n p := by
  apply List.ext_getElem
  · rw [List.length_ofFn,pathBytes_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

def pathToBits (n : ℕ) (c : m.Config) :
    AcceptedPath m acceptControl n c → AcceptedBits m acceptControl n c := fun p =>
  ⟨pathBits m acceptControl n p,by
    rw [pathBits_word]
    obtain ⟨d,ht,hd,ha⟩ := p.property
    exact (packet_accepts_iff m acceptControl n _ c).mpr
      ⟨List.ofFn p.val,d,List.length_ofFn,rfl,ht,hd,ha⟩⟩

theorem pathToBits_injective (n : ℕ) (c : m.Config) :
    Function.Injective (pathToBits m acceptControl n c) := by
  intro p q h
  apply Subtype.ext
  apply List.ofFn_injective
  apply encodeTokens_injective
  have hw := congrArg (fun b : AcceptedBits m acceptControl n c => List.ofFn b.val) h
  simpa only [pathToBits,pathBits_word,pathBytes] using hw

theorem pathToBits_surjective (n : ℕ) (c : m.Config) :
    Function.Surjective (pathToBits m acceptControl n c) := by
  intro bits
  obtain ⟨tokens,d,hlen,hword,ht,hd,ha⟩ :=
    (packet_accepts_iff m acceptControl n (List.ofFn bits.val) c).mp bits.property
  let choices : Fin n → Option Bool := fun i => tokens.get ⟨i.val,by rw [hlen]; exact i.isLt⟩
  have hchoices : List.ofFn choices = tokens := by
    apply List.ext_getElem
    · rw [List.length_ofFn,hlen]
    · intro i hi hj
      rw [List.getElem_ofFn]
      rfl
  let p : AcceptedPath m acceptControl n c := ⟨choices,d,by simpa only [hchoices] using ht,hd,ha⟩
  refine ⟨p,?_⟩
  apply Subtype.ext
  apply List.ofFn_injective
  rw [pathToBits,pathBits_word,pathBytes]
  exact (congrArg (fun xs => xs.flatMap Packet.encode) hchoices).trans hword.symm

def acceptedEquiv (n : ℕ) (c : m.Config) :
    AcceptedBits m acceptControl n c ≃ AcceptedPath m acceptControl n c :=
  (Equiv.ofBijective (pathToBits m acceptControl n c)
    ⟨pathToBits_injective m acceptControl n c,pathToBits_surjective m acceptControl n c⟩).symm

def pathCount {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) (T : Polynomial ℕ) (a : α) : ℕ :=
  Fintype.card (AcceptedPath m acceptControl (T.eval (ea.encode a).length) (initList m.core (ea.encode a)))

theorem path_count {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) (T : Polynomial ℕ) (a : α) :
    pathCount m acceptControl ea T a =
      witnessCount (2*T.eval (ea.encode a).length) (fun bits =>
        packetEval m acceptControl (T.eval (ea.encode a).length) bits (initList m.core (ea.encode a))) := by
  classical
  unfold pathCount
  rw [← Fintype.card_congr (acceptedEquiv m acceptControl _ _),Fintype.card_subtype,Finset.card_filter]
  unfold witnessCount countAccepted
  apply Finset.sum_congr rfl
  intro bits _
  cases h : packetEval m acceptControl (T.eval (ea.encode a).length) (List.ofFn bits)
      (initList m.core (ea.encode a)) <;> simp [h]

def sharpPWitness {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀)) (T : Polynomial ℕ) :
    SharpPWitness ea (pathCount m acceptControl ea T) where
  witnessLength := 2*T
  accept p := packetEval m acceptControl (T.eval (ea.encode p.1).length) p.2
    (initList m.core (ea.encode p.1))
  verifier := verifier m T acceptControl ea
  counts a := by
    simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat] using path_count m acceptControl ea T a

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
