// Elasticsearch types follow the snake_case JSON convention
/* eslint-disable @typescript-eslint/camelcase */

import { expect } from 'chai';
import { Mapping } from './es-types';
import { translateObjectMapping, getValidatorForMapping } from './validation';

describe('Elasticsearch Mapping Schema Validation @unit tests', () => {
  describe('mapping to schema translation', () => {
    context('when converting a mapping with most features', () => {
      const mapping: Mapping = {
        properties: {
          name: {
            dynamic: 'strict',
            properties: {
              first: { type: 'text' },
              last: { type: 'text' },
            },
          },
          user_id: {
            type: 'keyword',
            ignore_above: 100,
          },
          tags: {
            type: 'nested',
            properties: {
              id: { type: 'integer' },
              label: { type: 'keyword' },
            },
          },
        },
      };

      it('should get the correct schema without errors', () => {
        const schema = translateObjectMapping(mapping);
        expect(schema).to.deep.equal({
          type: ['object', 'null'],
          additionalProperties: true,
          properties: {
            name: {
              type: ['object', 'null'],
              additionalProperties: false,
              properties: {
                first: { type: ['string', 'null'] },
                last: { type: ['string', 'null'] },
              },
            },
            user_id: { type: ['string', 'null'] },
            tags: {
              type: ['array', 'null'],
              items: {
                type: 'object',
                properties: {
                  id: { type: ['integer', 'null'] },
                  label: { type: ['string', 'null'] },
                },
              },
            },
          },
        });
      });
    });
  });

  describe('validation function', () => {
    const mapping: Mapping = {
      properties: {
        name: {
          dynamic: 'strict',
          properties: {
            first: { type: 'text' },
            last: { type: 'text' },
          },
        },
        user_id: {
          type: 'keyword',
          ignore_above: 100,
        },
        tags: {
          type: 'nested',
          properties: {
            id: { type: 'integer' },
            label: { type: 'keyword' },
          },
        },
      },
    };
    const validate = getValidatorForMapping(mapping);

    context('when validating data conforming to schema', () => {
      const data = {
        name: { first: 'John', last: undefined },
        tags: [{ id: 1, label: 'Unicorn' }, { id: 2, label: 'Missing Surname' }],
      };
      it('should accept and keep all data', () => {
        const good = validate(data);
        expect(good).to.be.true;
        expect(validate.errors).to.be.null;
        expect(data).to.deep.equal({
          name: { first: 'John', last: undefined },
          tags: [{ id: 1, label: 'Unicorn' }, { id: 2, label: 'Missing Surname' }],
        });
      });
    });
    context('when validating data with unmapped fields', () => {
      const data = {
        first: 'John',
        last: 'Doe',
        user_id: 1,
      };
      it('should accept and keep unexpected data', () => {
        const ok = validate(data);
        expect(ok).to.be.true;
        expect(validate.errors).to.be.null;
        expect(data).to.deep.equal({
          first: 'John',
          last: 'Doe',
          user_id: '1',
        });
      });
    });
    context('when validating data with forbidden fields', () => {
      const data = {
        name: { full: 'John Doe' },
        user_id: 1,
      };
      it('should reject and report unexpected data', () => {
        const ok = validate(data);
        expect(ok).to.be.false;
        expect(validate.errors).to.be.an('array').that.is.not.empty;
      });
    });
    context('when validating data with compatible types', () => {
      const data = {
        user_id: 1,
        tags: [{ id: '1', label: 1 }, { id: '2', label: 2 }],
      };
      it('should accept and coerce all data', () => {
        const good = validate(data);
        expect(good).to.be.true;
        expect(validate.errors).to.be.null;
        expect(data).to.deep.equal({
          user_id: '1',
          tags: [{ id: 1, label: '1' }, { id: 2, label: '2' }],
        });
      });
    });
    context('when validating data with incompatible types', () => {
      const data = {
        tags: [{ id: 'a' }],
      };
      it('should reject and report errors', () => {
        const bad = !validate(data);
        expect(bad).to.be.true;
        expect(validate.errors).to.be.an('array').that.is.not.empty;
      });
    });
  });
});
