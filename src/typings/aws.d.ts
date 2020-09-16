declare module "aws-sdk/lib/signers/v4";

interface RequestSigner {
  new (): unknown;
  public addAuthorization();
}
