# Benchmarks for primitive-floats in Coq

Building
[Coq with primitive-floats](https://github.com/coq/coq/pull/9867),
then the
[posdef_check tactic](https://github.com/validsdp/validsdp/blob/posdef_check/theories/posdef_check.v)
with its dependencies takes around 75mn.

To make the process faster and less tedious, we prepared Docker images
gathering all this material prebuilt. They are available in this
[GitLab CI registry](https://gitlab.com/erikmd/docker-coq-primitive-floats/container_registry)
and these images are built from this
[Dockerfile](https://gitlab.com/erikmd/docker-coq-primitive-floats/blob/1.0/Dockerfile)
and [GitLab CI configuration](https://gitlab.com/erikmd/docker-coq-primitive-floats/blob/1.0/.gitlab-ci.yml).

The sequel of this document describes how to install Docker, and how
to run the benchmarks using Docker.

## Install Docker

Follow the official instructions and install [Docker Engine](https://docs.docker.com/engine/install/#server) for Linux.

> Note: the other user-friendly way of installing Docker, [Docker Desktop](https://docs.docker.com/get-docker/#supported-platforms), is known to [not work out-of-the-box for our use case](https://forums.docker.com/t/bind-mount-permissions-unexpected-mounting-as-root-root/129328/4) (due to a known issue with bind-mounts permissions).

### Convenience config for GNU/Linux and macOS

As the Docker daemon socket is owned by `root`, you will need to
prepend all `docker` CLI commands by `sudo`.
To do this automatically, a standard practice consists in adding the
following alias in your `~/.bashrc` file:

    alias docker='sudo docker'

**Warning:** to avoid this, some tutorials on the web suggest instead
to add your default Linux user to the `docker` group. *Don't do this*
on your personal workstation, because this would amount to provide the
default user with `root` permissions without `sudo`-like password
prompt protection.
[(cf. doc)](https://docs.docker.com/engine/security/security/#docker-daemon-attack-surface)

## Run the benchmarks using Docker

```bash
# cd "the_folder_containing_this_README"

docker pull registry.gitlab.com/erikmd/docker-coq-primitive-floats/master_coq-8.15-validsdp-1.0.1
# note that this may take a while as the compressed size of this Docker image is 998 MB,
# and you'll need enough space (in the '/' partition) as its uncompressed size is 3.14 GB.

docker run --rm -it -v "$PWD:$PWD" -w "$PWD" registry.gitlab.com/erikmd/docker-coq-primitive-floats/master_coq-8.15-validsdp-1.0.1 ./run.sh

pdflatex primfloat_comparison.tex
```

To just experience with primitive floats in Coq, one can simply run:

```bash
docker run --rm -it -v "$PWD:$PWD" -w "$PWD" registry.gitlab.com/erikmd/docker-coq-primitive-floats/master_coq-8.15-validsdp-1.0.1
$ coqtop  # or emacs (with proof-general)
Coq < Require Import Float.
Coq < Open Scope float_scope.
Coq < Eval vm_compute in 1 + 0.5.
```
