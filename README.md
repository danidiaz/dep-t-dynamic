# dep-t-dynamic

[![dep-t-dynamic.png](https://i.postimg.cc/DyP2zxcf/dep-t-dynamic.png)](https://postimg.cc/9rz38tSs)

## Relationship with the "registry" package

This library is heavily inspired in the [registry](https://hackage.haskell.org/package/registry) package, which provides a `Typeable`-based method for performing dependency injection.

This library is more restrictive and less ergonomic in some aspects, but it fits better with how [dep-t](https://hackage.haskell.org/package/dep-t) works. 

Some notable differences with **registry**:

- `Dep.Dynamic` only reports missing dependencies when the program logic first searches for them, while **registry** reports them when calling `withRegistry`.
- `Dep.Checked` and `Dep.SimpleChecked` do allow you to find missing dependencies before running the program logic, but they force you to explicitly list the dependencies of each new component you add to the environment, something that **registry** doesn't require.
- Unlike in **registry**, there are no specific [warmup](https://hackage.haskell.org/package/registry-0.2.1.0/docs/Data-Registry-Warmup.html#v:warmupOf) combinators. Allocating the resources required by a component must be done in an [`Applicative`](https://hackage.haskell.org/package/managed) "phase" of a [`Phased`](https://hackage.haskell.org/package/dep-t-0.6.0.0/docs/Dep-Env.html#t:Phased) environment. 
