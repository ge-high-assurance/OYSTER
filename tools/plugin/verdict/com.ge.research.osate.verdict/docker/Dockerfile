# Cache metadata in our image to make subsequent builds faster

ARG BUILDKIT_INLINE_CACHE=1

FROM ubuntu:22.04

RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive \
 && apt-get -y install --no-install-recommends \
    unzip \
    libgmp-dev \
    make \
    cmake \
    z3 \
    gcc \
    g++ \
# curl & ca-certificates needed for lfsc install script
    curl \ 
    ca-certificates \
 && rm -rf /var/lib/apt/lists/* \
 && adduser --disabled-password --gecos VERDICT verdict
 
# flex needs recommended libraries to be installed for cmake to recognize it
RUN apt-get update -qq && apt-get -y install flex

ADD --chmod=0755 https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.3/cvc5-Linux /usr/local/bin/cvc5
RUN chmod a+rx /usr/local/bin/cvc5

# Download LFSC
ENV LFSC_INSTALL_PATH=/opt/install_lfsc
RUN mkdir $LFSC_INSTALL_PATH
ADD --chmod=0755 https://raw.githubusercontent.com/kind2-mc/kind2/v1.7.0/lfsc/get-lfsc-checker.sh $LFSC_INSTALL_PATH/install_lfsc.sh
RUN chmod a+rx $LFSC_INSTALL_PATH/install_lfsc.sh
RUN mkdir /signatures
RUN $LFSC_INSTALL_PATH/install_lfsc.sh
RUN rm -r $LFSC_INSTALL_PATH

# Download required kind plf file (omitted from installation script)
ADD --chmod=0755 https://raw.githubusercontent.com/kind2-mc/kind2/v1.7.0/lfsc/signatures/kind.plf /signatures/kind.plf
RUN chmod a+rx /signatures/kind.plf

RUN printf "#!/bin/bash \
\n while getopts \":l:z:c:\" flag; do \
\n 	case \$flag in \
\n 		l) LFSC=\${OPTARG};; \
\n 		z) Z3=\${OPTARG};; \
\n 		c) CVC5=\${OPTARG};; \
\n 	esac \
\n done \
\n if [ \"\$Z3\" = \"true\" ]; then \
\n 	echo \"\"; \
\n 	echo \"*** Z3 Proof Validation ***\"; \
\n 	/proofs/certif/certificate_checker z3; \
\n 	echo \"\"; \
\n fi \
\n if [ \"\$CVC5\" = \"true\" ]; then \
\n 	echo \"\"; \
\n 	echo \"*** CVC5 Proof Validation ***\"; \
\n 	/proofs/certif/certificate_checker cvc5; \
\n 	echo \"\"; \
\n fi \
\n if [ \"\$LFSC\" = \"true\" ]; then \
\n 	echo \"\"; \
\n 	echo \"*** LFSC Proof Validation ***\"; \
\n 	/usr/bin/lfsc-check.sh /proofs/certificates.1/proof.lfsc; \
\n fi \
\n echo \"\"; \
\n echo \"Finished Proof Validation\"" > /bin/proof_validation.sh

RUN chmod a+rx /bin/proof_validation.sh

ENTRYPOINT ["/bin/proof_validation.sh"]
