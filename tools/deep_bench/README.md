# Running Benchmarks on an AWS Cluster

- set the `AWS_REGION` environment variable (e.g. `us-west-1` or `us-east-1`)

## Development

If doing development, save money by:

- setting `TF_VAR_instance_type` to `t2.small`
- setting `TF_VAR_cluster_size` to `1`