# Sandbox B

This sandbox contains more complicated policies and entities than those in
`sandbox_a`. In particular, the entities here have attributes, and the
policies use those attributes in deciding whether to allow or deny requests.

## policies_4.cedar

This policy allows only members of the `HardwareEngineering` department
with job level `>= 5` to view photos in the `device_prototypes` album.

Try this authorization request:

```shell
cargo run authorize \
    --principal 'User::"alice"' \
    --action 'Action::"view"' \
    --resource 'Photo::"prototype_v0.jpg"' \
    --policies policies_4.cedar \
    --entities entities.json
```

This should be allowed, because `alice` meets the requirements.

On the other hand, try other principals that don't meet the requirements:
`User::"stacey"` is in a different department, while `User::"ahmad"` is
in the correct department but not a high enough job level.

## policies_5.cedar

This policy set has an interesting rule where resources with the `private`
attribute set to `true` can only be viewed by their account's owner.

That means this authorization request should be denied, because the
photo's owner is not `User::"stacey"`:

```shell
cargo run authorize \
    --principal 'User::"stacey"' \
    --action 'Action::"view"' \
    --resource 'Photo::"alice_w2.jpg"' \
    --policies policies_5.cedar \
    --entities entities.json
```

But, `alice` should be allowed to view `alice_w2.jpg` (she's the owner), and
`stacey` should be allowed to view `vacation.jpg` (even though `stacey` isn't
the owner, that photo is not `private`, so `"alice's friends view policy"`
controls).

The other interesting part of this policy is that the `owner` attribute for
`Account` entities is _optional_, so the policy needs to insert a check that it's present before accessing it. For the second policy we see an
explicit check for  `resource.account has owner` which evaluates to `true` if the attribute is present. In that case, the expression after the `&&` will evaluate, and access the `owner` attribute's contents. If the `has` check evaluates to `false` then short-circuiting of `&&` will cause the attribute access to be skipped.

## policies_6.cedar

This policy set demonstrates the use of IP address values in Cedar.
It also demonstrates the `context` of a request, which is an additional input
along with `principal`, `action`, and `resource`.

With the default `context.json`, you should be able to see that `alice` is
allowed to view `vacation.jpg` (or any other resource transitively contained
in `Account::"alice"`):

```shell
cargo run authorize \
    --principal 'User::"alice"' \
    --action 'Action::"view"' \
    --resource 'Photo::"vacation.jpg"' \
    --context context.json \
    --policies policies_6.cedar \
    --entities entities.json
```

But, if you change the IP in `context.json` to one that is in the blocked range
in the policy, the access will not be allowed.

## Policy validation

You can validate if a policy conforms with the schema. Try the following:

```shell
cargo run validate \
  --policies policies_5.cedar \
  --schema schema.cedarschema
```

You can see that validation passes. If you look at `schema.cedarschema` you can see that it is larger than the schema used for `sandbox_a`. The `entity` declarations now contain information about some of the entity types' legal attributes. Notice that some attributes have a `?` by their name, which indicates they are optional. The `action` declarations also have a `context` field, which describes the legal shape of the `context` that can be passed in on authorization requests for that action.

If you try validating `policies_5_bad.cedar` instead, you'll see a validation failure. This is because the second policy (the `forbid` one) does not have the expression `resource.account has owner` prior to accessing the `owner` attribute; since that attribute is optional, the lack of a `has` check could result in a failure, so the validator flags it.

Now, continue on to `sandbox_c`, where we'll consider policy templates.
