FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y libgomp1

RUN mkdir theta
COPY . theta
WORKDIR theta
RUN ./gradlew theta-sts-cli:build && \
    mv subprojects/sts-cli/build/libs/theta-sts-cli-*-all.jar ../theta-sts-cli.jar
WORKDIR ..

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"
ENTRYPOINT ["java", "-jar", "theta-sts-cli.jar"]