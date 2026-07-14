# cp-307 Target Dynamics and Block-Length Bridge

## Implemented

`UniversalPaymentBlock.lean` now has the completed target dynamics API:

- target map monotonicity;
- equality of consecutive targets exactly at height-one times;
- strict consecutive target advance exactly at extra-height times;
- nonempty target fibers exactly at extra-height endpoints.

The stale footer was replaced.  Universal block geometry is now recorded as
complete.

For a nonempty universal payment block, Lean also proves:

```text
fiber card = endpoint - start + 1 = exact depth at start
```

This is the direct bridge from universal block length to the exact-depth
histogram.  The next layer is the universal complete-claim filter, endpoint
capacity concentration, and the direct universal ledger; these have not been
derived through the debt-only suffix.
