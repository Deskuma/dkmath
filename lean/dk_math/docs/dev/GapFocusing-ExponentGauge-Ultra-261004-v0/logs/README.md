# Archived evidence

The original tracked log bytes are stored in [evidence/](../evidence/README.md).
[The path index](../evidence/MANIFEST.md) identifies each original file and archive.

From the checkpoint directory, restore all original paths with:

```sh
python3 checks/archive_evidence.py restore
```

Restored evidence is ignored by Git. Run historical checks after restoration;
their original assertions and snapshot requirements remain unchanged.
