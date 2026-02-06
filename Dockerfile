FROM coqorg/coq:8.18.0
RUN opam update && \
    opam install -y coq-paco coq-equations && \
    opam clean -a -c -s --logs
WORKDIR /home/coq/LHL
COPY --chown=coq:coq _CoqProject .
COPY --chown=coq:coq Util/ ./Util/
COPY --chown=coq:coq Core/ ./Core/
COPY --chown=coq:coq Examples/ ./Examples/
COPY --chown=coq:coq README.md .
COPY --chown=coq:coq ebstack_structure.png .
COPY --chown=coq:coq build.sh .
RUN chmod +x build.sh
CMD ["/bin/bash"]