import AJV from "ajv";
import { ObjectMapping } from "./es-types";
export declare function translateObjectMapping(mapping: ObjectMapping): Record<string, unknown>;
export declare function getValidatorForMapping(mappings: ObjectMapping): AJV.ValidateFunction;
