module

public import Protovalidate.Cel.Format
import all Protovalidate.Cel.Format

/-!
Kernel-checked recognizer laws for `Protovalidate.Cel.Format`.

The formats are trusted code: what ties them to protovalidate is the
conformance battery (`//Test:format_corpus_test`), which is differential
testing over a finite corpus. These theorems are the complementary kind of
evidence — properties that hold for *every* input, proved once.

They cover the tractable formats. The headline is `ipv4Value?_lt`: the value an
accepted IPv4 address denotes really is a 32-bit number, which is what
`isIpPrefix`'s host-bit masking (`v % 2 ^ (32 - len)`) silently assumes. The
rest pin down documented shape claims (four dotted parts, the 253-character
hostname bound, the port range, the accepted IP versions) so they cannot drift
out of the implementation unnoticed.

Not covered: the URI grammar, the email grammar, and IPv6 — each would need
substantially more machinery, and none has a comparable arithmetic assumption
riding on it.
-/

@[expose] public section

namespace Cel.Format

/-! ## IPv4 -/

/-- An octet is at most 255 — the strictness `ipv4Octet?`'s final guard states. -/
theorem ipv4Octet?_le_255 {p : String} {v : Nat} (h : ipv4Octet? p = some v) : v ≤ 255 := by
  simp only [ipv4Octet?] at h
  repeat' first | split at h | cases h
  omega

/-- Accumulating octets base-256 keeps the running value under `256 ^ n`
(stated with the accumulator general so it inducts). -/
theorem ipv4Fold_bound (l : List String) : ∀ (acc v : Nat),
    l.foldlM (fun acc p => (ipv4Octet? p).map (acc * 256 + ·)) acc = some v →
    v + 1 ≤ (acc + 1) * 256 ^ l.length := by
  induction l with
  | nil =>
    intro acc v h
    simp only [List.foldlM] at h
    simp only [pure] at h
    injection h with h
    subst h
    simp
  | cons p rest ih =>
    intro acc v h
    simp only [List.foldlM] at h
    cases ho : ipv4Octet? p with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h
      simp only [Option.map_some] at h
      simp only [bind, Option.bind] at h
      have hb := ih _ _ h
      have h255 := ipv4Octet?_le_255 ho
      calc v + 1 ≤ (acc * 256 + o + 1) * 256 ^ rest.length := hb
        _ ≤ (acc + 1) * 256 * 256 ^ rest.length := Nat.mul_le_mul_right _ (by omega)
        _ = (acc + 1) * 256 ^ (rest.length + 1) := by rw [Nat.pow_succ]; ac_rfl

/-- An address that parses has exactly four dot-separated parts. -/
theorem ipv4Value?_length {s : String} {v : Nat} (h : ipv4Value? s = some v) :
    (s.splitOn ".").length = 4 := by
  simp only [ipv4Value?] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hlen
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
    exact hlen

/-- **The value an accepted IPv4 address denotes is a 32-bit number.** This is
what `isIpPrefix` assumes when it masks host bits with `v % 2 ^ (32 - len)`. -/
theorem ipv4Value?_lt {s : String} {v : Nat} (h : ipv4Value? s = some v) : v < 2 ^ 32 := by
  have hlen := ipv4Value?_length h
  simp only [ipv4Value?] at h
  split at h
  · exact absurd h (by simp)
  · have hb := ipv4Fold_bound _ 0 v h
    rw [hlen] at hb
    have h256 : (0 + 1) * (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    omega

theorem isIpv4_splitOn_length {s : String} (h : isIpv4 s = true) :
    (s.splitOn ".").length = 4 := by
  simp only [isIpv4, Option.isSome_iff_exists] at h
  obtain ⟨v, hv⟩ := h
  exact ipv4Value?_length hv

/-! ## Hostnames, ports, versions -/

/-- The documented 253-character bound really is enforced (trailing dot
included, as protovalidate counts it). -/
theorem isHostname_length {s : String} (h : isHostname s = true) : s.length ≤ 253 := by
  simp only [isHostname, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- An accepted port denotes a number in the 16-bit range. -/
theorem isPort_le {s : String} (h : isPort s = true) :
    s.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 ≤ 65535 := by
  simp only [isPort, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Only versions 0, 4 and 6 are ever accepted: `isIp(s, 5)` is false for every
`s`, matching protovalidate (whose conformance suite tests exactly that). -/
theorem isIp_version {s : String} {version : Int} (h : isIp s version = true) :
    version = 0 ∨ version = 4 ∨ version = 6 := by
  simp only [isIp] at h
  repeat' first | split at h | cases h
  all_goals simp_all

end Cel.Format
