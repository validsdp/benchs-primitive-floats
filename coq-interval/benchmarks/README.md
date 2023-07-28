# Benchmarks for primitive-floats in Coq

These benchmarks specifically focus on
[Coq with primitive-floats](https://coq.github.io/doc/master/refman/language/core/primitive.html#primitive-floats), and the [coq-interval tactic](https://gitlab.inria.fr/coqinterval/interval).

To make the process faster, less tedious, and reproducible, we
prepared Docker images gathering all this material prebuilt.

Building CoqInterval with its dependencies
from a [coqorg/coq](https://hub.docker.com/r/coqorg/coq) image takes around 17mn.

The resulting images are available in this
[GitLab CI registry](https://gitlab.com/erikmd/docker-coq-interval-primitive-floats/container_registry),
they are built from this
[Dockerfile](https://gitlab.com/erikmd/docker-coq-interval-primitive-floats/-/blob/2.0/Dockerfile)
and [GitLab CI configuration](https://gitlab.com/erikmd/docker-coq-interval-primitive-floats/-/blob/2.0/.gitlab-ci.yml).

The sequel of this document describes how to install Docker, and how
to run the benchmarks using Docker.

## Install Docker

Follow the official instructions and install [Docker Engine](https://docs.docker.com/engine/install/#server) for Linux.

> Note: the other user-friendly way of installing Docker, [Docker Desktop](https://docs.docker.com/get-docker/#supported-platforms), is known to [not work out-of-the-box for our use case](https://forums.docker.com/t/bind-mount-permissions-unexpected-mounting-as-root-root/129328/4) (due to a known issue with bind-mounts permissions).

### Convenience config for GNU/Linux and macOS

As the Docker daemon socket is owned by `root`, you will need to
prepend all `docker` CLI commands by `sudo`.
To do this automatically, a standard practice consists in
[adding an alias](https://stackoverflow.com/a/65956808/9164010)
in one's `~/.bashrc` file, e.g.:

    alias docker='sudo docker'

**Warning:** to avoid this, some tutorials on the web suggest instead
to add your default Linux user to the `docker` group. *Don't do this*
on your personal workstation, because this would amount to provide the
default user with `root` permissions without `sudo`-like password
prompt protection nor auditing.
[(cf. doc)](https://docs.docker.com/engine/security/security/#docker-daemon-attack-surface)

## Run the benchmarks using Docker

```bash
# cd "the_folder_containing_this_README"

docker pull registry.gitlab.com/erikmd/docker-coq-interval-primitive-floats/master_coq-8.15-interval-4.5.2
# note that this may take a while as the compressed size of this Docker image is 820 MB,
# and you'll need enough space (in the '/' partition) as its uncompressed size is 2.55 GB.

docker run --rm -it -v "$PWD:$PWD" -w "$PWD" registry.gitlab.com/erikmd/docker-coq-interval-primitive-floats/master_coq-8.15-interval-4.5.2 make

pdflatex primfloat_comparison.tex
```

To just experience with primitive floats in Coq, one can simply run:

```bash
docker run --rm -it -v "$PWD:$PWD" -w "$PWD" registry.gitlab.com/erikmd/docker-coq-interval-primitive-floats/master_coq-8.15-interval-4.5.2
$ coqtop
Coq < Require Import Floats.
Coq < Open Scope float_scope.
Coq < Eval vm_compute in 1 + 0.5.
```
