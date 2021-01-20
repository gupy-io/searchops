import { ValidateFunction } from "ajv";
import { ObjectMapping } from "./es-types";
export declare function translateObjectMapping(mapping: ObjectMapping): Record<string, unknown>;
export declare function getValidatorForMapping(mappings: ObjectMapping): ValidateFunction<unknown>;
