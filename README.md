# dep-t-dynamic

This library is a compation to [dep-t](https://hackage.haskell.org/package/dep-t) and in particular it complements the [`Dep.Env`](https://hackage.haskell.org/package/dep-t-0.6.0.0/docs/Dep-Env.html) module. It provides various types of dependency injection environments that are dynamically typed to some degree: missing dependencies are not detected at compilation time. Static checks are sacrificed for advantages like faster compilation.

[![dep-t-dynamic.png](https://i.postimg.cc/DyP2zxcf/dep-t-dynamic.png)](https://postimg.cc/9rz38tSs)

- **Dep.Dynamic** is the simplest dynamic environment, but it doesn't give many guarantees.
- **Dep.Checked** and **Dep.SimpleChecked** give greater guarantees at the cost of more ceremony and explicitness. **Dep.Checked** can only be used with the [`DepT`](https://hackage.haskell.org/package/dep-t-0.6.0.0/docs/Control-Monad-Dep.html) monad.

## Rationale

In [dep-t](https://hackage.haskell.org/package/dep-t), functions list their dependences on "injectable" components by means of [`Has`](https://hackage.haskell.org/package/dep-t-0.6.0.0/docs/Dep-Has.html) constraints. One step when creating your application is defining a big environment record whose fields are the components, and giving it suitable `Has` instances.

Environments often have two type parameters: 

- One is an `Applicative` "phase" that wraps each field and describes how far along we are in the process of constructing the environment (the `Identity` function correspond to a "finished" environment, ready to be used).
- The other is the effect monad which parameterizes each component in the environment.

Usually environments will be vanilla Haskell records. It has the advantage that "missing" dependencies are caught at compile-time. But using records might be undesirable is some cases:

- For environments with a big number of components, compiling the environment type might be slow.
- Defining the required `Has` instances for the environment might be a chore, even with the helpers from [`Dep.Env`](https://hackage.haskell.org/package/dep-t-0.6.0.0/docs/Dep-Env.html#g:2).  

## Relationship with the "registry" package

This library is heavily inspired in the [registry](https://hackage.haskell.org/package/registry) package, which provides a `Typeable`-based method for performing dependency injection.

This library is more restrictive and less ergonomic in some aspects, but it fits better with how [dep-t](https://hackage.haskell.org/package/dep-t) works. 

Some notable differences with **registry**:

- `Dep.Dynamic` only reports missing dependencies when the program logic first searches for them, while **registry** reports them when calling `withRegistry`.
- `Dep.Checked` and `Dep.SimpleChecked` do allow you to find missing dependencies before running the program logic, but they force you to explicitly list the dependencies of each new component you add to the environment, something that **registry** doesn't require.
- Unlike in **registry**, there are no specific [warmup](https://hackage.haskell.org/package/registry-0.2.1.0/docs/Data-Registry-Warmup.html#v:warmupOf) combinators. Allocating the resources required by a component must be done in an [`Applicative`](https://hackage.haskell.org/package/managed) "phase" of a [`Phased`](https://hackage.haskell.org/package/dep-t-0.6.0.0/docs/Dep-Env.html#t:Phased) environment. 
