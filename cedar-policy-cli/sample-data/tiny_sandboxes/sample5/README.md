## sample 5

### Authorize

 Can User::bob  view Photo:VacationPhoto94.jpg

 Decision: Allow

```
cargo run  authorize \
    --policies policy.cedar \
    --entities entity.json \
    --request-json request.json
```


### Validation

Is `policy.cedar` valid based on the schema `schema.cedarschema`

```
cargo run  validate \
    --policies policy.cedar \
    --schema schema.cedarschema
```

### Evaluate:

Evaluate a Cedar expression

```
cargo run  evaluate  \
    --request-json request.json \
    --entities entity.json \
     "principal.addr.isLoopback()"
```
