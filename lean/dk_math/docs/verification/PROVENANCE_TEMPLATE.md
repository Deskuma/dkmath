# <Case Title> Provenance

This record accompanies the
[`case landing page`](BREAKING_MATH_CASE_TEMPLATE.md). Do not fabricate missing
metadata and do not require a URL when no stable URL exists.

## Status vocabulary

Use separate fields rather than collapsing distinct statuses:

- `reported`: a claim appears in an identified source.
- `social-media post`: distributed through a social platform; this says
  nothing by itself about review.
- `published`: made publicly available at an identified location.
- `peer reviewed`: documented review status is known.
- `independently confirmed`: a distinct reconstruction or verification is
  documented.
- `Lean verified`: the exact recorded Lean proposition has a checked proof.
- `unknown`: the repository does not establish the status.

These labels may coexist. None implies another unless evidence is recorded.

## A. External Reported Source

- **Source title or description:** `<value | unknown>`
- **Author or account, when known:** `<value | unknown>`
- **Publication or post location, when known:** `<location | unknown>`
- **Stable URL or identifier:** `<value | not published | unknown | not applicable>`
- **First observed date:** `<date | unknown>`
- **Accessed date:** `<date | unknown>`
- **Source status:** `<reported | social-media post | published | peer reviewed | unknown>`
- **Independent confirmation status:** `<independently confirmed | not independently confirmed | unknown>`
- **Notes:** `<notes>`

## B. Formula Transcription

- **Exact formulas transcribed:**

  ```text
  <formulas or data exactly as recorded>
  ```

- **Transcription location in DkMath:** `<file and exact identifiers>`
- **Transcription checks performed:** `<checks>`
- **Missing information:** `<unknown | not published | not independently confirmed | not applicable | details>`
- **Ambiguities retained:** `<details or none>`

Do not silently repair or normalize source material in this section.

## C. DkMath-Independent Reconstruction

- **Independent calculations performed:** `<symbolic derivation, finite evaluation, cross-check, or none>`
- **Tools used:** `<Lean, hand calculation, CAS used only as guidance, etc.>`
- **Results independently reproduced:** `<exact results>`
- **Results not independently reproduced:** `<exact results or not applicable>`
- **Known uncertainties:** `<uncertainties or none>`

“Independently reconstructed” describes the calculation route, not historical
priority or peer-review status.

## D. DkMath-Specific Formalization Choices

- **Lean encoding choices:** `<types, representations, coordinate order, definitions>`
- **Normalization or coordinate changes:** `<exact changes | not applicable>`
- **Transport or coercion choices:** `<details | not applicable>`
- **Summit theorem identifier:** `<DkMath.Hackathon.<CaseName>.<summitTheorem>>`
- **Material not taken from the source:** `<helper lemmas, organization, normalization, consequences>`
- **Axiom-audit location:** `<DkMathTest path>`

## E. Later Interpretation Layers

- **DkMath interpretation added later:** `<concepts and modules | not applicable>`
- **Dependency on the core certificate:** `<description>`
- **Claims introduced by interpretation:** `<claims or none>`
- **Claims not attributed to the source:** `<list>`

Interpretation modules must be identified separately from the source claim and
the independent formal certificate.

## Missing-Information Policy

Use explicit values such as:

```text
unknown
not published
not independently confirmed
not applicable
```

Do not infer dates from identifiers, infer authorship from reposts, convert a
social-media report into publication or peer-review status, or treat Lean
verification as evidence of historical priority.
