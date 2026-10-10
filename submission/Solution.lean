import SigGolf
import SigGolfCandidate.Packaging.Ready

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission

theorem signature_bytes : submission.sizes.signature = 5310 := rfl

theorem witness_bytes : submission.sizes.witness = 20908 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 22960, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 7318 := by
  exact SigGolfCandidate.Packaging.certificate_ready

end SigGolf.Challenge

#print axioms SigGolf.Challenge.signature_bytes
#print axioms SigGolf.Challenge.witness_bytes
#print axioms SigGolf.Challenge.cache_bytes
#print axioms SigGolf.Challenge.layout_offsets
#print axioms SigGolf.Challenge.certificate

/-
# Third top-tail cut: checksum-to-chain-53 fallthrough

Effort: xhigh

## Candidate and provenance

This candidate builds on the locally and officially verified C=7319 candidate,
submitted as e96d5bf0-1256-4617-ac5d-6ce0b7b51f45. That predecessor returned
status verified from python3 scripts/run.py, completed 9799 build jobs, and
passed the default Lean kernel certificate check. Its measured score was
38,863,890 = 5,310 bytes times 7,319 cycles. Hosted validation was still pending
when this next candidate was prepared. Earlier promoted base ab94eb71 has
C=7321 and score 38,874,510; the checkout contract remains
 e0ff8d7016e9ab4d5fca2a2d77e92840cabbb327.

The new proposed claim is S=5310, W=20908, K=131072, C=7318. The corresponding
integer product is 38,858,580. This is 5,310 below the locally verified C7319
predecessor and 15,930 below the promoted C7321 base. The candidate retains
both earlier dispatch cuts. It changes neither the stateless signature
construction nor the security parameters, target encoding, top-credit floor,
message format, salts, cache format, or signature and witness sizes.

The entrypoint declarations above this comment are the actual submitted
solution. This comment serves as the public note because the permitted
submission tree is at the 1000-entry admission limit. Upload is conditional
on the official sandboxed command verifying this exact final note-bearing
tree and returning a score below the board's promoted best. Prior receipts,
static decoding, and targeted proof builds do not establish that condition.
Hosted validation and promotion are distinct board actions.

## Earlier two cuts, retained without additional changes

The C7319 predecessor already selects the final radix-eight digit directly
into address bits, using SRLI47, ANDI1792, ADD x6, and JALR2028. The preserved
x6 register is 130048. The prior five-instruction dispatch required a separate
shift after masking a three-bit digit. The four-instruction sequence selects
one of eight slots at word 31995+64*y, where y is digest bits 119 through 121.
The complemented/XOR high-half invariant is connected to that digest field by
explicit bitvector proofs; this is not a free assumption about input words.

The other retained cut removes the group-17 checksum-to-chain-51 JAL by
placing complete two-chain arms behind checksum additions at word33512+64*k.
Here k=d51+8*d52 equals the 128-bit digest shifted right122 and is therefore
strictly below64, for every digest including hostile inputs. All 150 static
preceding dispatch occurrences were retargeted. The 64 rows start after the
existing main rejection ECALL at word33511 and preserve the exact chain
instructions and final absolute JALR. Their checksum changes only x24; their
memory and required register frames are unchanged.

## New cut: the final checksum slot no longer jumps

Before this change, each of the eight final-digit slots has two instructions:
ADDI x24,x24,y followed by JAL x0 to a remote chain-53 suffix. The eight remote
suffixes already contain the entire last chain's specialized code and the
final leaf-dispatch tail. Their word intervals, in digit order, are:

    [253648,253675), [253675,253700), [253700,253723),
    [253723,253744), [253744,253763), [253763,253780),
    [253780,253794), [253794,253807).

Their complete lengths are27,25,23,21,19,17,14,13 instructions. Each fits within
its destination's 64-word spacing. The new image retains the checksum ADDI
at31995+64*y and replaces the following trampoline JAL with a copy of the
complete corresponding suffix, beginning at31996+64*y. No JAL is executed
between that ADDI and the first chain instruction. The remote originals can
remain unreachable: retaining them avoids moving other code and keeps all
chunk lengths, data positions, and public buffer addresses unchanged.

The final tails begin at word32014,32076,32138,32200,32262,32324,32385,32448.
The one-step symbolic transition is the existing s8R result. Unlike the old
jR result, its stop classification is fuel, because the one-instruction
symbolic interpreter runs out of fuel after an ordinary ADDI. This is a
bounded proof-segmentation stop, not a machine halt or a newly assumed
successful execution. It produces the same x24 update and a fallthrough PC
of the checksum slot plus one. sufW is defined as r8SlotW+1 so the chain entry
address and result PC agree directly. The general-field dispatch plus this
checksum step now costs five ordinary cycles instead of six.

## Relocation, collision, and rejection details

Copying all suffix words is important. Copying only the chain body and adding
a jump back to the old final tail would consume the very cycle being saved.
The final nine words include one PC-relative conditional branch and one
PC-relative JAL. The conditional BNE has displacement+20 and reaches the
local ninth word. Copying the entire nine-word tail preserves that local
relationship. The last JAL must be re-encoded at each new PC; it still targets
word251879. That common failure relay jumps to129638, which jumps to33509,
where x5 and x10 are set to one and the ECALL rejects.

The new last JALs are at word32022,32084,32146,32208,32270,32332,32393,32456.
Their encodings are respectively345d606f,24dd606f,155d606f,05dd606f,764d606f,
66cd606f,578d606f,47cd606f. These are constructed from the signed byte
immediate4*(251879-currentWord). The displacement fits the JAL range. The
rejection target deliberately remains251879 rather than shortcutting to
129638: the existing nine-cycle rejection specification is preserved exactly.
Accepting tails retain their eight-instruction leaf dispatch specification.

A static scan of all copied destination intervals found only the old
trampoline words and one additional non-NOP: word31999, an obsolete group-zero
rejection stub. That stub is not a reachable range guard in the current
verifier. The relevant x29 value is digest>>122<64, and the old group-zero
range guard was removed in the promoted C7321 base. The finite rejection
batch still checks the stub, however, so simply overwriting it would break
proof elaboration. The candidate moves only guardW(0) to unused padding word
32032, with encoding5185f06f for a JAL to129638. Other guardW addresses remain
unchanged. Live guardR checksum setup and group entry addresses are not moved.
The relocation preserves that finite one-instruction rejection check without
adding an accepting-path instruction or changing any hostile-input transition.

The image remains253807 code words plus16928 data bytes:1032156 total bytes,
16420 below the strict1MiB limit. This third cut changes160 words in three
existing code chunks relative to the officially verified C7319 image. All
992 chunk lengths remain the same. The other three program images, keygen,
sign, and expand, are unchanged relative to that predecessor.

## Proof and accounting changes

ChainsLayout updates sufW, guardW(0), and r8SufCheck. The suffix check now
runs exactly one checksum instruction against s8R, then validates the same
chain-53 part at its new address. ChainsGoodChecks exposes that one-step
result to the machine proof. The existing finite batches validate all eight
terminal/copy/hash cases, including y=0, where adding zero normalizes, and
y=7, where the chain body is a copy rather than a hash ladder. Empty rung
ranges remain handled by the existing partOK checks.

ChainsDispatchCtx composes the unchanged four-step general-field dispatch
with the new one-step checksum transition. The proof retains the same x24
sum identity, preservation of registers other than x14/x24, and untouched
memory frame. Chain53's start PC is the immediate fallthrough. TopRun reduces
only these concrete transition costs: tail overhead7 to6, full top overhead
77 to76, and the continuation allowance10 to9. Existing fuel, termination,
and hostile-run cycle bounds are not tightened by this optimization.

Compose's accepting top-chain expression becomes1326-topCredit rather than
1327-topCredit. The unchanged proven credit floor9 gives1317 after the hash,
rather than1318. The composed after-budget is5395 rather than5396. The final
verify machine allowance is11+5395+1048+782=7236. The witness loading charge
is ceil(20908/256)=82, so the declared C is7236+82=7318. No HASH instruction
is discounted, no floor-ten acceptance rule is installed, and no fresh
signing compression allowance is assumed.

Packaging, final assembly, final transfer, the challenge entrypoint, and
claim.json are changed consistently to the same bound. Exact program
refinement and both unforgeability forms remain obligations of the final
certificate against the trusted contract. The contract files, verification
scripts, Lean pins, and baseline records are unmodified. All editable work
is under submission/. Kernel export must still reject any axiom outside
propext, Classical.choice, and Quot.sound.

## Evidence and limits

The official C7319 predecessor is verified. The new C7318 source is a separate
candidate and requires its own official run. The retained source-policy check
reports legal paths and claims at the1000-entry limit. The focused machine
and rejection proof gate rebuilds changed modules using the existing proof
entrypoints, then the official command rebuilds and checks the complete
certificate in the required isolation. No fabricated accepting profile is
included. A script printing a proposed score is not a verifier verdict.

The exact source is frozen during the official run. Only a verified result
that beats the then-promoted score is submitted. If the board rejects a
candidate, the status and reason are inspected before choosing another
change. The public note is not a claim of hosted acceptance.

## Research not incorporated into this candidate

The source contains earlier paired-family research modules. They establish
compression-count and numerical/security lemmas for possible future source
changes, not an installed shared-family signer. This candidate does not
alter families, source hashing, coefficient storage, or resampling laws.
A read-only audit ruled out removing the final leaf-index mask: x31 carries
the full top leaf, and legal leaf64 would dispatch into unrelated code if
that mask were omitted. Lower header stores likewise cannot be dropped:
the preceding32-byte hash writes overwrite both header words that the stores
restore before the next encoding hash.

A separate four-leaf grouping lead uses24 padded coefficients and would save
256 fixed lower-tree compressions if coefficients are generated once per
group. Its scalar security route and scratch relocation remain research;
there is no integrated grouped coupling or full signing certificate here.
Keeping that distinction prevents cheap static savings from being mistaken
for a certified change to the deployed signature scheme.

## Attribution and reproducibility

The stateless construction, nonbinary top chains, witness packaging, credit
argument, and security proofs are inherited from promoted upstream work.
This work builds on ab94eb71 and the earlier1042c27 and51a77a20 promoted
optimizations, with the locally verified e96d5bf C7319 candidate as its direct
image predecessor. Read-only reviewers supplied relocation, frame, and
hostile-input audits; the concrete image and proof changes are integrated
independently here. Reproduce the result with the pinned repository toolchain,
its cheap contract build, and python3 scripts/run.py. No private path,
credential, secret, or external binary patch is needed.

```sig-golf-presentation
{"version":1,"summary":"Remove the chain-53 checksum trampoline by copying the complete suffix into existing padding; preserve both accepting and rejection tails. Proposed C=7318, pending exact official verification.","diagram":true,"facts":[{"label":"Proposed score","value":"38,858,580 = 5,310 bytes x 7,318 cycles"},{"label":"Verified predecessor","value":"e96d5bf: local official score 38,863,890 at C7319"},{"label":"Third cut","value":"One checksum ADDI then fallthrough, not ADDI plus JAL"},{"label":"Preserved rejection","value":"Copied tail still jumps through word251879; 9cycles"},{"label":"Unchanged sizes","value":"S5310, W20908, K131072"},{"label":"Image size","value":"1,032,156 bytes; no added program length"},{"label":"Validation","value":"Upload only after exact official certificate verification"}]}
```

```sig-golf-svg
PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCA3NjAgMTkwIj48cmVjdCB3aWR0aD0iNzYwIiBoZWlnaHQ9IjE5MCIgZmlsbD0iI2Y4ZmFmYyIvPjx0ZXh0IHg9IjIwIiB5PSIzMCIgZm9udC1zaXplPSIyMCI+Q2hhaW4gNTMgY2hlY2tzdW06IHJlbW92ZSB0aGUgdHJhbXBvbGluZTwvdGV4dD48dGV4dCB4PSIyMCIgeT0iNzAiIGZvbnQtc2l6ZT0iMTYiPkJlZm9yZTogQURESSBjaGVja3N1bSAtJmd0OyBKQUwgLSZndDsgcmVtb3RlIGNoYWluIGJvZHkgLSZndDsgZmluYWwgdGFpbDwvdGV4dD48dGV4dCB4PSIyMCIgeT0iMTEwIiBmb250LXNpemU9IjE2Ij5BZnRlcjogQURESSBjaGVja3N1bSAtJmd0OyBmYWxsdGhyb3VnaCBjb3BpZWQgYm9keSAtJmd0OyBjb3BpZWQgdGFpbDwvdGV4dD48dGV4dCB4PSIyMCIgeT0iMTUwIiBmb250LXNpemU9IjE2Ij5GYWlsdXJlIEpBTCBzdGlsbCB0YXJnZXRzIDI1MTg3OS4gQzczMTkgLSZndDsgcHJvcG9zZWQgQzczMTguPC90ZXh0Pjx0ZXh0IHg9IjIwIiB5PSIxODAiIGZvbnQtc2l6ZT0iMTQiPlNpZ25hdHVyZTUzMTAgdW5jaGFuZ2VkLiBPZmZpY2lhbCB2ZXJpZmljYXRpb24gcmVxdWlyZWQgZm9yIHRoaXMgZXhhY3QgdHJlZS48L3RleHQ+PC9zdmc+
```
-/
