BEGIN;

CREATE TABLE IF NOT EXISTS public.runes
(
    number numeric NOT NULL,
    rune_id character varying(32) NOT NULL,
    spaced_rune character varying(64) NOT NULL,
    divisibility smallint NOT NULL,
    symbol character varying(4),
    etching character varying(64) NOT NULL,
    premine numeric NOT NULL,
    terms_amount numeric,
    terms_cap numeric,
    terms_height_start numeric,
    terms_height_end numeric,
    terms_offset_start numeric,
    terms_offset_end numeric,
    mints numeric NOT NULL,
    burned numeric NOT NULL,
    block numeric NOT NULL,
    timestamp timestamp with time zone NOT NULL,
    turbo boolean NOT NULL DEFAULT FALSE,
    weight integer NOT NULL DEFAULT 100,
    CONSTRAINT runes_pkey PRIMARY KEY (rune_id),
    CONSTRAINT runes_spaced_rune_key UNIQUE (spaced_rune)
);

CREATE TABLE IF NOT EXISTS public.rune_balances
(
    rune_id character varying(32) NOT NULL,
    address character varying(64) NOT NULL,
    amount numeric NOT NULL,
    CONSTRAINT rune_balances_pkey PRIMARY KEY (rune_id, address),
    CONSTRAINT rune_balances_rune_id_fkey FOREIGN KEY (rune_id) REFERENCES public.runes (rune_id)
);

CREATE TABLE IF NOT EXISTS public.rs_transactions
(
    txid character varying(64) NOT NULL,
    transaction json NOT NULL,
    CONSTRAINT rs_transactions_pkey PRIMARY KEY (txid)
);

CREATE TABLE IF NOT EXISTS public.rune_transactions
(
    rune_id character varying(32) NOT NULL,
    txid character varying(64) NOT NULL,
    block numeric NOT NULL,
    timestamp timestamp with time zone NOT NULL,
    CONSTRAINT rune_transactions_pkey PRIMARY KEY (rune_id, txid),
    CONSTRAINT rune_transactions_rune_id_fkey FOREIGN KEY (rune_id) REFERENCES public.runes (rune_id),
    CONSTRAINT rune_transactions_txid_fkey FOREIGN KEY (txid) REFERENCES public.rs_transactions (txid)
);

CREATE TABLE IF NOT EXISTS public.address_transactions
(
    address character varying(64) NOT NULL,
    txid character varying(64) NOT NULL,
    CONSTRAINT address_transactions_pkey PRIMARY KEY (address, txid),
    CONSTRAINT address_transactions_txid_fkey FOREIGN KEY (txid) REFERENCES public.rs_transactions (txid)
);

END;
