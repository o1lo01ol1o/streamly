# Compilation Options

Recommended GHC options are: 

  `-O2 -fspec-constr-recursive=10 -fmax-worker-args=16`

`-fspec-constr-recursive` is needed for better stream fusion by enabling
the `SpecConstr` optimization in more cases.

`-fmax-worker-args` is needed for better stream fusion by enabling the
`SpecConstr` optimization in some important cases.

In some cases, you may need to use `-funfolding-use-threshold` to make sure
that the combinators fuse. The default value of this option is `60`. Increasing
this default value can be detrimental in general, therefore, increase only if
you suspect an issue.  Hopefully GHC will fix this so that it is not needed in
future.  Some known examples:

* use a value of `75` to fuse `S.chunksOf n (A.writeN n)`.
* use a value of `150` to fully fuse `S.splitSuffixOn`.

At the very least `-O` compilation option is required. In some cases, the
program may exhibit memory hog with default optimization options.  For example,
the following program, if compiled without an optimization option, is known to
hog memory:

```
main = S.drain $ S.concatMap S.fromList $ S.repeat []
```

# Multi-core Parallelism

Concurrency without a threaded runtime may be a bit more efficient. Do not use
threaded runtime unless you really need multi-core parallelism. To get
multi-core parallelism use the following GHC options:

  `-threaded -with-rtsopts "-N"`

# Compiler Versions

GHC 8.2.2 may hog memory and hang when building certain application using
streamly (particularly the benchmark programs in the streamly package).
Therefore we recommend avoiding using the GHC version 8.2.x.
